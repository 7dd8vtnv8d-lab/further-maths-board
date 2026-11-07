// Encrypted relay fallback for Further Maths Board.
// When two devices can't connect directly (mobile data, strict Wi-Fi), messages travel through
// free public MQTT brokers instead. Everything is end-to-end encrypted (AES-GCM) with a key derived
// from the board link, and the topic name is a hash of it, so brokers can neither read nor find boards.
(() => {
'use strict';
const enc = new TextEncoder(), dec = new TextDecoder();
const BROKERS = [
  { url: 'wss://public.cloud.shiftr.io', user: 'public', pass: 'public' },
  { url: 'wss://broker.emqx.io:8084/mqtt' },
  { url: 'wss://broker.hivemq.com:8884/mqtt' },
];
const CHUNK = 48000, MAX_CHUNKS = 400, HDR = 17;

const u8 = a => a instanceof Uint8Array ? a : new Uint8Array(a);
function concat(parts){ let n = 0; for (const p of parts) n += p.length; const o = new Uint8Array(n); let i = 0; for (const p of parts) { o.set(p, i); i += p.length; } return o; }
function varint(n){ const out = []; do { let b = n % 128; n = Math.floor(n / 128); if (n > 0) b |= 128; out.push(b); } while (n > 0); return u8(out); }
function strU8(s){ const b = enc.encode(s); return concat([u8([b.length >> 8, b.length & 255]), b]); }
function pkt(first, body){ return concat([u8([first]), varint(body.length), body]); }
const toHex = b => Array.from(b, x => x.toString(16).padStart(2, '0')).join('');
function fromHex(h){ const o = new Uint8Array(h.length / 2); for (let i = 0; i < o.length; i++) o[i] = parseInt(h.substr(i * 2, 2), 16); return o; }

// Minimal MQTT 3.1.1 client over WebSocket: connect, subscribe to one topic, publish QoS 0.
class Conn {
  constructor(cfg, topic, onPayload, onState){
    this.cfg = cfg; this.topic = topic; this.onPayload = onPayload; this.onState = onState;
    this.ok = false; this.closed = false; this.delay = 1000; this.ws = null; this.buf = new Uint8Array(0);
    this.connect();
  }
  connect(){
    if (this.closed) return;
    let ws;
    try { ws = new WebSocket(this.cfg.url, ['mqtt']); } catch (e) { this.retryLater(); return; }
    ws.binaryType = 'arraybuffer'; this.ws = ws; this.buf = new Uint8Array(0);
    ws.onopen = () => {
      const cid = ('fmwb' + Math.random().toString(36).slice(2, 12) + Date.now().toString(36)).slice(0, 23);
      let flags = 0x02; const tail = [strU8(cid)];
      if (this.cfg.user) { flags |= 0x80; tail.push(strU8(this.cfg.user)); }
      if (this.cfg.pass) { flags |= 0x40; tail.push(strU8(this.cfg.pass)); }
      try { ws.send(pkt(0x10, concat([strU8('MQTT'), u8([4, flags, 0, 30]), ...tail]))); } catch (e) {}
    };
    ws.onmessage = ev => { if (this.ws === ws && ev.data instanceof ArrayBuffer) this.feed(new Uint8Array(ev.data)); };
    const down = () => {
      if (this.ws !== ws) return;
      this.ws = null; clearInterval(this.ping); clearTimeout(this.openTimer);
      if (this.ok) { this.ok = false; this.onState(); }
      try { ws.close(); } catch (e) {}
      this.retryLater();
    };
    ws.onclose = down; ws.onerror = down;
    clearTimeout(this.openTimer);
    this.openTimer = setTimeout(() => { if (this.ws === ws && !this.ok) down(); }, 10000);
  }
  retryLater(){
    if (this.closed) return;
    clearTimeout(this.rt);
    this.rt = setTimeout(() => this.connect(), this.delay + Math.random() * 500);
    this.delay = Math.min(this.delay * 2, 30000);
  }
  feed(chunk){
    this.buf = this.buf.length ? concat([this.buf, chunk]) : chunk;
    for (;;) {
      const b = this.buf; if (b.length < 2) return;
      let mul = 1, len = 0, i = 1, byte;
      do { if (i >= b.length) return; byte = b[i++]; len += (byte & 127) * mul; mul *= 128; if (i > 5) { this.kill(); return; } } while (byte & 128);
      if (b.length < i + len) return;
      const type = b[0] >> 4, flags = b[0] & 15, body = b.subarray(i, i + len);
      this.buf = b.subarray(i + len);
      this.handle(type, flags, body);
    }
  }
  handle(type, flags, body){
    if (type === 2) { // CONNACK
      if (body.length >= 2 && body[1] === 0) {
        this.ok = true; this.delay = 1000; clearTimeout(this.openTimer);
        try { this.ws.send(pkt(0x82, concat([u8([0, 1]), strU8(this.topic), u8([0])]))); } catch (e) {}
        clearInterval(this.ping);
        this.ping = setInterval(() => { try { if (this.ws && this.ws.readyState === 1) this.ws.send(u8([0xC0, 0])); } catch (e) {} }, 20000);
        this.onState();
      } else this.kill();
    } else if (type === 3 && body.length >= 2) { // PUBLISH
      const tl = (body[0] << 8) | body[1]; let p = 2 + tl;
      if ((flags >> 1) & 3) p += 2;
      if (p <= body.length) this.onPayload(body.slice(p));
    }
  }
  kill(){ try { if (this.ws) this.ws.close(); } catch (e) {} }
  publish(payload){
    const ws = this.ws;
    if (!this.ok || !ws || ws.readyState !== 1 || ws.bufferedAmount > 4e6) return false;
    try { ws.send(pkt(0x30, concat([strU8(this.topic), payload]))); return true; } catch (e) { return false; }
  }
  close(){
    this.closed = true; clearTimeout(this.rt); clearInterval(this.ping); clearTimeout(this.openTimer);
    const ws = this.ws; this.ws = null; this.ok = false;
    if (ws) { try { if (ws.readyState === 1) ws.send(u8([0xE0, 0])); ws.close(); } catch (e) {} }
  }
}

async function create(code, myTab, onMessage, onState){
  const base = await crypto.subtle.importKey('raw', enc.encode('fmwb-relay-v1:' + code), 'PBKDF2', false, ['deriveKey']);
  const key = await crypto.subtle.deriveKey({ name: 'PBKDF2', salt: enc.encode('further-maths-board'), iterations: 150000, hash: 'SHA-256' },
    base, { name: 'AES-GCM', length: 256 }, false, ['encrypt', 'decrypt']);
  const th = new Uint8Array(await crypto.subtle.digest('SHA-256', enc.encode('fmwb-topic-v1:' + code)));
  const topic = 'fmwb/v1/' + toHex(th.slice(0, 16));
  const tabBytes = fromHex(myTab);
  let seq = crypto.getRandomValues(new Uint32Array(1))[0];
  const partial = new Map(), seen = new Set(), seenQ = [];
  let closed = false;

  async function onPayload(p){
    if (closed || p.length < HDR || p[0] !== 1) return;
    const from = toHex(p.subarray(1, 9)); if (from === myTab) return;
    const dv = new DataView(p.buffer, p.byteOffset, p.byteLength);
    const id = dv.getUint32(9), idx = dv.getUint16(13), total = dv.getUint16(15);
    const mk = from + ':' + id;
    if (seen.has(mk) || !total || idx >= total || total > MAX_CHUNKS) return;
    let body;
    if (total === 1) body = p.subarray(HDR);
    else {
      let e = partial.get(mk);
      if (!e) { e = { parts: new Array(total), got: 0, t: Date.now() }; partial.set(mk, e); }
      if (!e.parts[idx]) { e.parts[idx] = p.slice(HDR); e.got++; }
      if (e.got < total) return;
      partial.delete(mk); body = concat(e.parts);
    }
    seen.add(mk); seenQ.push(mk); if (seenQ.length > 4000) seen.delete(seenQ.shift());
    if (body.length < 29) return;
    try {
      const pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: body.subarray(0, 12) }, key, body.subarray(12));
      const m = JSON.parse(dec.decode(pt));
      if (m && typeof m.k === 'string') onMessage(m.k, m.d, from, typeof m.to === 'string' ? m.to : null);
    } catch (e) { /* not for us, or tampered with: ignore */ }
  }
  const conns = BROKERS.map(cfg => new Conn(cfg, topic, onPayload, () => onState(conns.filter(c => c.ok).length)));
  const sweep = setInterval(() => { const now = Date.now(); for (const [k, e] of partial) if (now - e.t > 30000) partial.delete(k); }, 10000);

  async function send(kind, data, to){
    if (closed) return;
    const plain = enc.encode(JSON.stringify({ k: kind, d: data, to: to || null }));
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const body = concat([iv, new Uint8Array(await crypto.subtle.encrypt({ name: 'AES-GCM', iv }, key, plain))]);
    const total = Math.max(1, Math.ceil(body.length / CHUNK)); if (total > MAX_CHUNKS) return;
    seq = (seq + 1) >>> 0;
    for (let i = 0; i < total; i++) {
      const hdr = new Uint8Array(HDR), dv = new DataView(hdr.buffer);
      hdr[0] = 1; hdr.set(tabBytes, 1); dv.setUint32(9, seq); dv.setUint16(13, i); dv.setUint16(15, total);
      const payload = concat([hdr, body.subarray(i * CHUNK, (i + 1) * CHUNK)]);
      for (const c of conns) c.publish(payload);
    }
  }
  return {
    send,
    up: () => conns.filter(c => c.ok).length,
    close(){ closed = true; clearInterval(sweep); conns.forEach(c => c.close()); },
  };
}
window.FMRelay = { create };
})();
