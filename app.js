// Further Maths Board: shared infinite whiteboard. No accounts, no server: browsers sync directly.
(() => {
'use strict';
// Set after the first publish so the Invite box can show a real link.

const $ = s => document.querySelector(s);
const $$ = s => Array.from(document.querySelectorAll(s));
const app = $('#app'), cv = $('#board'), ctx = cv.getContext('2d');
const store = {
  get(k){ try{ return localStorage.getItem(k); }catch(e){ return null; } },
  set(k,v){ try{ localStorage.setItem(k,v); return true; }catch(e){ return false; } },
};

/* ---------------- theme ---------------- */
const T = { dark:false, paper:'#fbfbf7', grid:'', gridMajor:'', fg:'#1a2030', muted:'#5b6475', accent:'#2747c7', chrome:'#fff', line:'#dde2ea' };
function readTheme(){
  const cs = getComputedStyle(document.documentElement);
  const g = n => cs.getPropertyValue(n).trim();
  T.dark = g('--is-dark') === '1';
  T.paper = g('--paper'); T.grid = g('--grid'); T.gridMajor = g('--grid-major');
  T.fg = g('--fg'); T.muted = g('--muted'); T.accent = g('--accent'); T.chrome = g('--chrome'); T.line = g('--line');
  dirty();
}
new MutationObserver(readTheme).observe(document.documentElement, {attributes:true, attributeFilter:['data-theme','class','style']});
try{ matchMedia('(prefers-color-scheme: dark)').addEventListener('change', readTheme); }catch(e){}

const INK = { ink:['#1a1f2b','#eef1f6'], blue:['#2350d8','#86a0ff'], red:['#d43a2f','#ff7d70'], green:['#1c8a4a','#5cd08e'], orange:['#e07b12','#ffad55'], purple:['#7b3fc4','#c6a0ff'] };
const HL = { yellow:['#ffd400','#e8c400'], pink:['#ff5fa2','#ff6fae'], cyan:['#2ec9ff','#3fcfff'], lime:['#8fdc2c','#9be640'] };
const colOf = k => (INK[k] || HL[k] || INK.ink)[T.dark ? 1 : 0];
const GCOLS = ['blue','red','green','purple'];
const PEN_SIZES = [2, 4, 8], HL_SIZES = [12, 22, 34];

/* ---------------- state ---------------- */
const cam = { x:-500, y:-320, z:1 };
let W = 0, H = 0, dpr = 1, rect = {left:0, top:0};
const objs = new Map();
let order = [], orderDirty = true;
let tool = 'pen';
const prefs = { ink:'ink', hl:'yellow', size:1, hlSize:1, dash:false, bg:store.get('fmwb:bg') || 'squares', fingerPans:store.get('fmwb:fp') === '1' };
const selection = new Set();
let undoStack = [], redoStack = [];
let board = null;
let editing = null;          // {o, isNew}
let gesture = null;
let draft = null;            // my in-progress object
let spaceDown = false;
let lastWorld = null;        // last pointer world pos
let peers = [];
let followPeer = null;
const drafts = new Map();    // remote ink drafts
const trails = new Map();    // laser trails peer -> [{x,y,t}]
const rid = () => Math.random().toString(36).slice(2, 9) + Date.now().toString(36).slice(-5);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const r1 = v => Math.round(v * 10) / 10;
const r3 = v => Math.round(v * 1000) / 1000;

/* ---------------- geometry ---------------- */
let bboxCache = new WeakMap();
const measureCtx = document.createElement('canvas').getContext('2d');
const FONT = '"Atkinson Hyperlegible", system-ui, sans-serif';
function textLines(o){ return String(o.s).split('\n'); }
function bbox(o){
  let b = bboxCache.get(o); if (b) return b;
  switch (o.t) {
    case 'stroke': {
      let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity; const p = o.p;
      for (let i = 0; i < p.length; i += 2) { const x = p[i], y = p[i+1]; if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
      const m = o.sw / 2; b = [o.x + x0 - m, o.y + y0 - m, o.x + x1 + m, o.y + y1 + m]; break; }
    case 'line': { const m = o.sw * (o.a ? 5 : 1); b = [Math.min(o.x, o.x+o.ex) - m, Math.min(o.y, o.y+o.ey) - m, Math.max(o.x, o.x+o.ex) + m, Math.max(o.y, o.y+o.ey) + m]; break; }
    case 'text': {
      measureCtx.font = `${o.fs}px ${FONT}`; let w = 0; const L = textLines(o);
      for (const l of L) w = Math.max(w, measureCtx.measureText(l).width);
      b = [o.x, o.y, o.x + Math.max(w, o.fs * 0.5), o.y + L.length * o.fs * 1.3]; break; }
    default: { const m = (o.sw || 0) / 2; b = [o.x - m, o.y - m, o.x + o.w + m, o.y + o.h + m]; }
  }
  bboxCache.set(o, b); return b;
}
function distSeg(px, py, ax, ay, bx, by){
  const dx = bx - ax, dy = by - ay, l = dx*dx + dy*dy;
  let t = l ? ((px-ax)*dx + (py-ay)*dy) / l : 0; t = clamp(t, 0, 1);
  const x = ax + t*dx - px, y = ay + t*dy - py; return Math.sqrt(x*x + y*y);
}
function inBox(b, x, y, pad){ return x >= b[0]-pad && x <= b[2]+pad && y >= b[1]-pad && y <= b[3]+pad; }
function hit(o, x, y, tol, forErase){
  const b = bbox(o); if (!inBox(b, x, y, tol)) return false;
  if (o.t === 'stroke') {
    const p = o.p, t = tol + o.sw/2;
    if (p.length === 2) return Math.hypot(o.x+p[0]-x, o.y+p[1]-y) <= t;
    for (let i = 0; i < p.length - 2; i += 2) if (distSeg(x, y, o.x+p[i], o.y+p[i+1], o.x+p[i+2], o.y+p[i+3]) <= t) return true;
    return false;
  }
  if (o.t === 'line') return distSeg(x, y, o.x, o.y, o.x+o.ex, o.y+o.ey) <= tol + o.sw/2 + (o.a ? o.sw*2 : 0);
  if (forErase) {
    if (o.t === 'image' || o.t === 'graph') return false;
    if (o.t === 'rect') { const d = Math.min(Math.abs(x-o.x), Math.abs(x-o.x-o.w), Math.abs(y-o.y), Math.abs(y-o.y-o.h)); return d <= tol + o.sw; }
    if (o.t === 'ellipse') { const rx = o.w/2, ry = o.h/2, cx = o.x+rx, cy = o.y+ry; const k = Math.hypot((x-cx)/rx, (y-cy)/ry); return Math.abs(k-1) * Math.min(rx, ry) <= tol + o.sw; }
  }
  return true;
}
const ERASABLE = new Set(['stroke','line','rect','ellipse','text','axes']);
const RESIZABLE = new Set(['image','graph','rect','ellipse','axes','text']);

/* ---------------- object hygiene (remote data is untrusted) ---------------- */
const TYPES = new Set(['stroke','line','rect','ellipse','text','image','graph','axes']);
const num = v => typeof v === 'number' && isFinite(v);
function clean(o){
  if (!o || typeof o !== 'object' || !TYPES.has(o.t) || typeof o.id !== 'string' || !/^[a-z0-9]{4,24}$/.test(o.id)) return null;
  if (!num(o.x) || !num(o.y) || Math.abs(o.x) > 1e7 || Math.abs(o.y) > 1e7) return null;
  const r = { id:o.id, t:o.t, x:o.x, y:o.y, z: num(o.z) ? o.z : 0, c: (typeof o.c === 'string' && (INK[o.c] || HL[o.c])) ? o.c : 'ink', by: typeof o.by === 'string' ? o.by.slice(0, 24) : '' };
  const sw = num(o.sw) ? clamp(o.sw, 0.05, 400) : 2;
  switch (o.t) {
    case 'stroke':
      if (!Array.isArray(o.p) || o.p.length < 2 || o.p.length > 24000 || o.p.length % 2 || !o.p.every(num)) return null;
      r.p = o.p; r.sw = sw; r.hl = !!o.hl; break;
    case 'line':
      if (!num(o.ex) || !num(o.ey)) return null; r.ex = o.ex; r.ey = o.ey; r.sw = sw; r.a = !!o.a; r.d = !!o.d; break;
    case 'text':
      if (typeof o.s !== 'string') return null; r.s = o.s.slice(0, 4000); r.fs = num(o.fs) ? clamp(o.fs, 1, 2000) : 22; break;
    case 'image':
      if (typeof o.src !== 'string' || !/^data:image\/(png|jpeg|webp|gif);base64,[A-Za-z0-9+/=]+$/.test(o.src)) return null; r.src = o.src;
      // fallthrough to box
    case 'rect': case 'ellipse': case 'axes': case 'graph':
      if (!num(o.w) || !num(o.h) || o.w <= 0 || o.h <= 0) return null; r.w = o.w; r.h = o.h; r.sw = sw; r.d = !!o.d;
      if (o.t === 'graph') {
        if (!Array.isArray(o.fx)) return null; r.fx = o.fx.slice(0, 4).map(s => typeof s === 'string' ? s.slice(0, 120) : '');
        const g = ['xa','xb','ya','yb']; for (const k of g) { if (!num(o[k])) return null; r[k] = o[k]; }
        if (!(r.xb > r.xa) || !(r.yb > r.ya)) return null;
      }
      break;
  }
  return r;
}

/* ---------------- rendering ---------------- */
let needsDraw = true, rafOn = false, baseDirty = true;
// The board is drawn in two layers: a cached base (paper + saved objects + selection) and a light overlay
// (ink being drawn, other people's cursors, laser). While you write, only the overlay is redrawn.
const baseCv = document.createElement('canvas'), bctx = baseCv.getContext('2d');
function dirty(){ baseDirty = true; needsDraw = true; if (!rafOn) { rafOn = true; requestAnimationFrame(frame); } }
function overlay(){ needsDraw = true; if (!rafOn) { rafOn = true; requestAnimationFrame(frame); } }
function resize(){
  const r = cv.getBoundingClientRect(); rect = r;
  dpr = Math.min(window.devicePixelRatio || 1, 2.5);
  W = r.width; H = r.height; cv.width = baseCv.width = Math.round(W * dpr); cv.height = baseCv.height = Math.round(H * dpr);
  dirty(); sendView();
}
new ResizeObserver(resize).observe(cv);

const pathCache = new WeakMap();
function strokePath(o, live){
  let p = live ? null : pathCache.get(o); if (p) return p;
  p = new Path2D(); const a = o.p, n = a.length / 2, ox = o.x, oy = o.y;
  p.moveTo(ox + a[0], oy + a[1]);
  if (n === 1) p.lineTo(ox + a[0] + 0.01, oy + a[1]);
  else if (n === 2) p.lineTo(ox + a[2], oy + a[3]);
  else {
    for (let i = 1; i < n - 1; i++) {
      const x1 = ox + a[2*i], y1 = oy + a[2*i+1], x2 = ox + a[2*i+2], y2 = oy + a[2*i+3];
      p.quadraticCurveTo(x1, y1, (x1 + x2) / 2, (y1 + y2) / 2);
    }
    p.lineTo(ox + a[2*n-2], oy + a[2*n-1]);
  }
  if (!live) pathCache.set(o, p); return p;
}
function arrowHead(c, x1, y1, x2, y2, sw){
  const ang = Math.atan2(y2 - y1, x2 - x1), L = Math.max(10 * Math.min(1, sw / 2) + 6, sw * 4.2), sp = 0.45;
  c.beginPath(); c.moveTo(x2 - L * Math.cos(ang - sp), y2 - L * Math.sin(ang - sp)); c.lineTo(x2, y2); c.lineTo(x2 - L * Math.cos(ang + sp), y2 - L * Math.sin(ang + sp)); c.stroke();
}
const imgCache = new Map();
function getImg(src){
  let im = imgCache.get(src);
  if (!im) { im = new Image(); im.onload = dirty; im.src = src; imgCache.set(src, im); }
  return im;
}
const compiled = new Map();
function getFn(src){
  if (compiled.has(src)) return compiled.get(src);
  let f = null; try { f = compile(src, {allowX:true}); } catch(e) { f = null; }
  compiled.set(src, f); return f;
}
function niceStep(raw){ const p = Math.pow(10, Math.floor(Math.log10(raw))); const f = raw / p; return (f < 1.5 ? 1 : f < 3.5 ? 2 : f < 7.5 ? 5 : 10) * p; }
function fmtTick(v){ const s = (Math.abs(v) < 1e-9 ? 0 : v).toPrecision(6); return String(parseFloat(s)); }

function drawGraph(c, o, scale){
  const { x, y, w, h, xa, xb, ya, yb } = o;
  const sx = v => x + (v - xa) / (xb - xa) * w, sy = v => y + h - (v - ya) / (yb - ya) * h;
  const fsz = clamp(Math.min(w, h) / 26, 7, 40), lw = Math.max(0.6, 1 / scale);
  c.save();
  c.fillStyle = T.dark ? '#1b2029' : '#ffffff'; c.fillRect(x, y, w, h);
  c.beginPath(); c.rect(x, y, w, h); c.clip();
  const stx = niceStep((xb - xa) / 8), sty = niceStep((yb - ya) / 7);
  c.strokeStyle = T.dark ? 'rgba(140,170,230,.13)' : 'rgba(40,70,140,.11)'; c.lineWidth = lw;
  c.beginPath();
  for (let v = Math.ceil(xa / stx) * stx; v <= xb; v += stx) { c.moveTo(sx(v), y); c.lineTo(sx(v), y + h); }
  for (let v = Math.ceil(ya / sty) * sty; v <= yb; v += sty) { c.moveTo(x, sy(v)); c.lineTo(x + w, sy(v)); }
  c.stroke();
  const ax0 = clamp(sx(0), x, x + w), ay0 = clamp(sy(0), y, y + h);
  c.strokeStyle = T.dark ? 'rgba(230,235,245,.7)' : 'rgba(26,32,48,.75)'; c.lineWidth = lw * 1.4;
  c.beginPath(); c.moveTo(x, ay0); c.lineTo(x + w, ay0); c.moveTo(ax0, y); c.lineTo(ax0, y + h); c.stroke();
  c.fillStyle = T.dark ? 'rgba(220,226,240,.75)' : 'rgba(40,46,62,.8)'; c.font = `${fsz}px ${FONT}`;
  c.textAlign = 'center'; c.textBaseline = 'top';
  for (let v = Math.ceil(xa / stx) * stx; v <= xb; v += stx) { if (Math.abs(v) < stx / 2) continue; const px = sx(v); if (px < x + fsz || px > x + w - fsz) continue; c.fillText(fmtTick(v), px, Math.min(ay0 + 3, y + h - fsz - 2)); }
  c.textAlign = 'right'; c.textBaseline = 'middle';
  for (let v = Math.ceil(ya / sty) * sty; v <= yb; v += sty) { if (Math.abs(v) < sty / 2) continue; const py = sy(v); if (py < y + fsz || py > y + h - fsz) continue; c.fillText(fmtTick(v), Math.max(ax0 - 4, x + fsz * 2.2), py); }
  // curves
  const N = clamp(Math.round(w * scale), 120, 1800), E = { deg:false, ans:0 };
  let ly = y + 6;
  o.fx.forEach((src, i) => {
    if (!src || !src.trim()) return;
    const f = getFn(src); const colr = colOf(GCOLS[i % 4]);
    c.strokeStyle = colr; c.lineWidth = Math.max(1.6 / scale, w / 260); c.lineJoin = 'round';
    if (f) {
      c.beginPath(); let pen = false, prevY = 0;
      for (let k = 0; k <= N; k++) {
        const xv = xa + (xb - xa) * k / N; let yv;
        try { yv = f(xv, E); } catch(e) { yv = NaN; }
        if (!isFinite(yv)) { pen = false; continue; }
        const py = sy(yv), px = sx(xv);
        if (pen && Math.abs(py - prevY) > h * 1.5) pen = false;
        if (Math.abs(py - y) > h * 50) { pen = false; prevY = py; continue; }
        if (pen) c.lineTo(px, py); else c.moveTo(px, py);
        pen = true; prevY = py;
      }
      c.stroke();
    }
    c.textAlign = 'left'; c.textBaseline = 'top'; c.font = `700 ${fsz * 1.05}px ${FONT}`;
    const label = 'y = ' + src.replace(/^\s*y\s*=\s*/i, '') + (f ? '' : '  (can’t read this)');
    c.fillStyle = T.dark ? 'rgba(27,32,41,.85)' : 'rgba(255,255,255,.85)';
    const tw = c.measureText(label).width; c.fillRect(x + 6, ly - 2, tw + 8, fsz * 1.35);
    c.fillStyle = colr; c.fillText(label, x + 10, ly); ly += fsz * 1.5;
  });
  c.restore();
  c.strokeStyle = T.line; c.lineWidth = lw; c.strokeRect(x, y, w, h);
}

function drawObj(c, o, scale, live){
  switch (o.t) {
    case 'stroke':
      c.strokeStyle = colOf(o.c); c.lineWidth = o.sw; c.lineCap = 'round'; c.lineJoin = 'round';
      if (o.hl) { c.save(); c.globalAlpha = T.dark ? 0.42 : 0.38; if (!T.dark) c.globalCompositeOperation = 'multiply'; c.stroke(strokePath(o, live)); c.restore(); }
      else c.stroke(strokePath(o, live));
      break;
    case 'line':
      c.strokeStyle = colOf(o.c); c.lineWidth = o.sw; c.lineCap = 'round'; c.lineJoin = 'round';
      if (o.d) c.setLineDash([o.sw * 3.2, o.sw * 2.6]);
      c.beginPath(); c.moveTo(o.x, o.y); c.lineTo(o.x + o.ex, o.y + o.ey); c.stroke(); c.setLineDash([]);
      if (o.a) arrowHead(c, o.x, o.y, o.x + o.ex, o.y + o.ey, o.sw);
      break;
    case 'rect': case 'ellipse':
      c.strokeStyle = colOf(o.c); c.lineWidth = o.sw; c.lineJoin = 'round';
      if (o.d) c.setLineDash([o.sw * 3.2, o.sw * 2.6]);
      c.beginPath();
      if (o.t === 'rect') c.rect(o.x, o.y, o.w, o.h); else c.ellipse(o.x + o.w/2, o.y + o.h/2, o.w/2, o.h/2, 0, 0, Math.PI * 2);
      c.stroke(); c.setLineDash([]); break;
    case 'axes': {
      const cx = o.x + o.w/2, cy = o.y + o.h/2, colr = colOf(o.c), fs = clamp(Math.min(o.w, o.h) / 11, 10, 60);
      c.strokeStyle = colr; c.lineWidth = o.sw; c.lineCap = 'round'; c.lineJoin = 'round';
      c.beginPath(); c.moveTo(o.x, cy); c.lineTo(o.x + o.w, cy); c.moveTo(cx, o.y + o.h); c.lineTo(cx, o.y); c.stroke();
      arrowHead(c, o.x, cy, o.x + o.w, cy, o.sw); arrowHead(c, cx, o.y + o.h, cx, o.y, o.sw);
      c.fillStyle = colr; c.font = `italic ${fs}px ${FONT}`; c.textBaseline = 'top'; c.textAlign = 'right';
      c.fillText('x', o.x + o.w, cy + fs * 0.35); c.textAlign = 'left'; c.fillText('y', cx + fs * 0.4, o.y);
      c.textAlign = 'right'; c.font = `${fs * 0.85}px ${FONT}`; c.fillText('O', cx - fs * 0.25, cy + fs * 0.2);
      break; }
    case 'text': {
      c.fillStyle = colOf(o.c); c.font = `${o.fs}px ${FONT}`; c.textBaseline = 'top'; c.textAlign = 'left';
      const L = textLines(o); for (let i = 0; i < L.length; i++) c.fillText(L[i], o.x, o.y + i * o.fs * 1.3 + o.fs * 0.12);
      break; }
    case 'image': {
      const im = getImg(o.src);
      if (im.complete && im.naturalWidth) c.drawImage(im, o.x, o.y, o.w, o.h);
      else { c.fillStyle = T.dark ? '#232936' : '#eceff4'; c.fillRect(o.x, o.y, o.w, o.h); }
      break; }
    case 'graph': drawGraph(c, o, scale); break;
  }
}

function drawGrid(c){
  if (prefs.bg === 'plain') return;
  let step = 25; while (step * cam.z < 11) step *= 4;
  const major = step * 4;
  const x0 = cam.x, y0 = cam.y, x1 = cam.x + W / cam.z, y1 = cam.y + H / cam.z;
  c.save(); c.setTransform(dpr, 0, 0, dpr, 0, 0);
  const sxp = v => Math.round((v - cam.x) * cam.z) + 0.5, syp = v => Math.round((v - cam.y) * cam.z) + 0.5;
  if (prefs.bg === 'squares') {
    c.lineWidth = 1;
    c.strokeStyle = T.grid; c.beginPath();
    for (let v = Math.floor(x0 / step) * step; v <= x1; v += step) { if (Math.round(v / step) % 4 === 0) continue; c.moveTo(sxp(v), 0); c.lineTo(sxp(v), H); }
    for (let v = Math.floor(y0 / step) * step; v <= y1; v += step) { if (Math.round(v / step) % 4 === 0) continue; c.moveTo(0, syp(v)); c.lineTo(W, syp(v)); }
    c.stroke();
    c.strokeStyle = T.gridMajor; c.beginPath();
    for (let v = Math.floor(x0 / major) * major; v <= x1; v += major) { c.moveTo(sxp(v), 0); c.lineTo(sxp(v), H); }
    for (let v = Math.floor(y0 / major) * major; v <= y1; v += major) { c.moveTo(0, syp(v)); c.lineTo(W, syp(v)); }
    c.stroke();
  } else {
    let ds = 25; while (ds * cam.z < 22) ds *= 2;
    c.fillStyle = T.gridMajor; c.beginPath();
    for (let vx = Math.floor(x0 / ds) * ds; vx <= x1; vx += ds)
      for (let vy = Math.floor(y0 / ds) * ds; vy <= y1; vy += ds) c.rect(Math.round((vx - cam.x) * cam.z) - 1, Math.round((vy - cam.y) * cam.z) - 1, 2.2, 2.2);
    c.fill();
  }
  c.restore();
}

function sortedObjs(){
  if (orderDirty) { order = Array.from(objs.values()).sort((a, b) => (a.z - b.z) || (a.id < b.id ? -1 : 1)); orderDirty = false; }
  return order;
}

function frame(){
  rafOn = false;
  const now = performance.now();
  stepFollow();
  if (followPeer) { rafOn = true; requestAnimationFrame(frame); }
  let animating = false;
  if (!needsDraw && !trails.size) return;
  needsDraw = false;
  const px = 1 / cam.z, world = [dpr * cam.z, 0, 0, dpr * cam.z, -cam.x * cam.z * dpr, -cam.y * cam.z * dpr];
  if (baseDirty) {
    baseDirty = false;
    const c = bctx;
    c.setTransform(1, 0, 0, 1, 0, 0);
    c.fillStyle = T.paper; c.fillRect(0, 0, baseCv.width, baseCv.height);
    drawGrid(c);
    c.setTransform(...world);
    const vx0 = cam.x, vy0 = cam.y, vx1 = cam.x + W / cam.z, vy1 = cam.y + H / cam.z;
    const hidden = editing ? editing.o.id : null;
    for (const o of sortedObjs()) {
      if (o.id === hidden) continue;
      const b = bbox(o); if (b[2] < vx0 || b[0] > vx1 || b[3] < vy0 || b[1] > vy1) continue;
      drawObj(c, o, cam.z, false);
    }
    if (selection.size) {
      c.strokeStyle = T.accent; c.lineWidth = 1.5 * px; c.setLineDash([5 * px, 4 * px]);
      for (const id of selection) { const o = objs.get(id); if (!o) continue; const b = bbox(o); c.strokeRect(b[0] - 4*px, b[1] - 4*px, b[2] - b[0] + 8*px, b[3] - b[1] + 8*px); }
      c.setLineDash([]);
      const h = handleBox(); if (h) { c.fillStyle = T.chrome; c.strokeStyle = T.accent; c.lineWidth = 2 * px; c.fillRect(h[0], h[1], h[2], h[2]); c.strokeRect(h[0], h[1], h[2], h[2]); }
    }
    if (gesture && gesture.mode === 'marquee') {
      const g = gesture, x = Math.min(g.x0, g.x1), y = Math.min(g.y0, g.y1);
      c.fillStyle = 'rgba(80,110,230,.08)'; c.strokeStyle = T.accent; c.lineWidth = px;
      c.fillRect(x, y, Math.abs(g.x1 - g.x0), Math.abs(g.y1 - g.y0)); c.strokeRect(x, y, Math.abs(g.x1 - g.x0), Math.abs(g.y1 - g.y0));
    }
  }
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  ctx.drawImage(baseCv, 0, 0);
  ctx.setTransform(...world);
  // other people's ink and shapes while they draw
  ctx.save(); ctx.globalAlpha = 0.85;
  for (const [k, d] of drafts) { if (now - d.last > 6000) { drafts.delete(k); continue; } drawObj(ctx, d.o, cam.z, true); }
  for (const p of peers) {
    if (!p.presence || !p.presence.dr) continue;
    const o = clean(Object.assign({ id:'draftxx' }, p.presence.dr)); if (o) drawObj(ctx, o, cam.z, true);
  }
  ctx.restore();
  if (draft) drawObj(ctx, draft, cam.z, true);
  // laser trails
  for (const [k, tr] of trails) {
    while (tr.pts.length && now - tr.pts[0].t > 900) tr.pts.shift();
    if (!tr.pts.length) { trails.delete(k); continue; }
    animating = true;
    for (let i = 1; i < tr.pts.length; i++) {
      const a = tr.pts[i-1], b = tr.pts[i], age = (now - b.t) / 900;
      ctx.strokeStyle = tr.col; ctx.globalAlpha = Math.max(0, 1 - age); ctx.lineCap = 'round';
      ctx.lineWidth = (6 * (1 - age) + 1.5) * px; ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
    }
    ctx.globalAlpha = 1;
  }
  // screen-space: cursors with name tags, eraser ring
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  for (const p of peers) {
    if (!p.presence || !p.primary) continue;
    const cur = p.presence.cur; if (!Array.isArray(cur) || !num(cur[0]) || !num(cur[1])) continue;
    let dp = curDisp.get(p.peer);
    if (!dp || Math.hypot(cur[0] - dp.x, cur[1] - dp.y) * cam.z > 600) { dp = { x: cur[0], y: cur[1] }; curDisp.set(p.peer, dp); }
    dp.x += (cur[0] - dp.x) * 0.3; dp.y += (cur[1] - dp.y) * 0.3;
    if (Math.hypot(cur[0] - dp.x, cur[1] - dp.y) * cam.z > 0.5) animating = true;
    const sx = (dp.x - cam.x) * cam.z, sy = (dp.y - cam.y) * cam.z;
    if (sx < -40 || sy < -40 || sx > W + 40 || sy > H + 40) continue;
    const colr = safeCol(p.presence.col), name = safeName(p.presence.name);
    ctx.fillStyle = colr; ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.moveTo(sx, sy); ctx.lineTo(sx + 3.5, sy + 15); ctx.lineTo(sx + 7, sy + 9.5); ctx.lineTo(sx + 13, sy + 8.5); ctx.closePath(); ctx.fill(); ctx.stroke();
    ctx.font = `700 12px ${FONT}`; const tw = ctx.measureText(name).width;
    ctx.beginPath(); ctx.roundRect ? ctx.roundRect(sx + 12, sy + 14, tw + 12, 20, 6) : ctx.rect(sx + 12, sy + 14, tw + 12, 20); ctx.fill();
    ctx.fillStyle = '#fff'; ctx.textBaseline = 'middle'; ctx.textAlign = 'left'; ctx.fillText(name, sx + 18, sy + 24.5);
  }
  if (tool === 'eraser' && lastWorld && !spaceDown) {
    const sx = (lastWorld.x - cam.x) * cam.z, sy = (lastWorld.y - cam.y) * cam.z;
    ctx.strokeStyle = T.fg; ctx.lineWidth = 1.2; ctx.beginPath(); ctx.arc(sx, sy, 10, 0, 6.2832); ctx.stroke();
  }
  if (editing) positionEditor();
  $('#empty').hidden = objs.size > 0 || !!draft || drafts.size > 0 || !S.open;
  if (animating && !rafOn) { needsDraw = true; rafOn = true; requestAnimationFrame(frame); }
}
const safeCol = c => (typeof c === 'string' && /^#[0-9a-f]{6}$/i.test(c)) ? c : '#8892a6';
const safeName = n => (typeof n === 'string' && n.trim()) ? n.trim().slice(0, 24) : 'Guest';

function handleBox(){
  if (selection.size !== 1 || tool !== 'select') return null;
  const o = objs.get([...selection][0]); if (!o || !RESIZABLE.has(o.t)) return null;
  const b = bbox(o), s = 10 / cam.z; return [b[2] + 4/cam.z - s/2, b[3] + 4/cam.z - s/2, s];
}

/* ---------------- camera ---------------- */
const toWorld = (sx, sy) => ({ x: cam.x + sx / cam.z, y: cam.y + sy / cam.z });
function zoomAt(sx, sy, nz){
  nz = clamp(nz, 0.04, 24); const w = toWorld(sx, sy);
  cam.z = nz; cam.x = w.x - sx / nz; cam.y = w.y - sy / nz; camChanged();
}
function camChanged(){ $('#zoomPct').textContent = Math.round(cam.z * 100) + '%'; dirty(); sendView(); }
function centerOn(x, y, z){ if (z) cam.z = clamp(z, 0.04, 24); cam.x = x - W / 2 / cam.z; cam.y = y - H / 2 / cam.z; camChanged(); }
function fitAll(){
  if (!objs.size) { centerOn(0, 0, 1); return; }
  let b = [Infinity, Infinity, -Infinity, -Infinity];
  for (const o of objs.values()) { const q = bbox(o); b = [Math.min(b[0], q[0]), Math.min(b[1], q[1]), Math.max(b[2], q[2]), Math.max(b[3], q[3])]; }
  const z = clamp(Math.min((W - 160) / (b[2] - b[0] || 1), (H - 200) / (b[3] - b[1] || 1)), 0.04, 2);
  centerOn((b[0] + b[2]) / 2, (b[1] + b[3]) / 2, z);
}
function stopFollow(silent){ if (!followPeer) return; followPeer = null; presenceSet({ follow:null }); renderPeople(); if (!silent) toast('Stopped following'); }
function stepFollow(){
  if (!followPeer) return;
  const p = peers.find(q => q.peer === followPeer);
  if (!p) { stopFollow(true); toast('They left the board'); return; }
  const v = p.presence && p.presence.v;
  if (Array.isArray(v) && v.every(num)) {
    const tz = clamp(v[2] * Math.min(W / (v[3] || W), H / (v[4] || H)), 0.04, 24);
    const tx = v[0] - W / 2 / tz, ty = v[1] - H / 2 / tz;
    if (Math.abs(tx - cam.x) > 0.01 || Math.abs(ty - cam.y) > 0.01 || Math.abs(tz - cam.z) > 0.0005) { cam.x = tx; cam.y = ty; cam.z = tz; $('#zoomPct').textContent = Math.round(cam.z * 100) + '%'; needsDraw = true; baseDirty = true; }
  }
}

/* ---------------- identity, members, peer-to-peer sync ---------------- */
// One identity per browser: every tab and every board shares this id and name.
let me = (() => {
  let id = store.get('fmwb:uid');
  if (!id || !/^[a-z0-9]{12,24}$/.test(id)) { id = (rid() + rid() + rid()).replace(/[^a-z0-9]/g, '').slice(0, 16); store.set('fmwb:uid', id); }
  return { id, name: store.get('fmwb:name') || '' };
})();
const APP_ID = 'further-maths-board-v1';
const LIB_URL = './trystero.js';
const PALETTE = ['#e5484d','#f76b15','#e8a10c','#7bb31a','#2fa36b','#1f6f43','#12a594','#00a2c7','#1f6fe0','#5146d6','#8a4fd8','#c837ab','#ff5fa2','#a07a4f','#5d6b82','#9b2c2c'];
const UID_RE = /^[a-z0-9]{12,24}$/;
const recs = new Map();            // id -> {id, o|null, v, by}  (last writer wins, deletes kept as tombstones)
const members = new Map();         // uid -> {uid, name, col, j, v}
const pres = new Map();            // peerId -> {uid, p, t}
let clock = 0;
let meta = { name:'', v:0, by:'' };
const S = { room:null, act:{}, bc:null, relay:null, relayUp:0, netStart:0, token:0, lib:null, open:false };
// Each open tab gets its own id, so messages arriving both directly and through the relay can be matched up.
const TAB = Array.from(crypto.getRandomValues(new Uint8Array(8)), b => b.toString(16).padStart(2, '0')).join('');
const TAB_RE = /^[0-9a-f]{16}$/;
const peer2tab = new Map(), tab2peer = new Map(), known = new Set();
const curDisp = new Map();
let presState = {};

function hslHex(h, s, l){ s /= 100; l /= 100; const k = n => (n + h / 30) % 12, a = s * Math.min(l, 1 - l), f = n => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1))); return '#' + [f(0), f(8), f(4)].map(x => Math.round(x * 255).toString(16).padStart(2, '0')).join(''); }
const myColor = () => (members.get(me.id) || {}).col || '#8892a6';
const colorFor = uid => (members.get(uid) || {}).col || null;
function nameTakenBy(n){ const l = n.trim().toLowerCase(); for (const m of members.values()) if (m.uid !== me.id && m.name.trim().toLowerCase() === l) return m; return null; }
function pickColor(){
  const used = new Set([...members.values()].filter(m => m.uid !== me.id).map(m => m.col));
  const free = PALETTE.filter(c => !used.has(c));
  if (free.length) return free[Math.floor(Math.random() * free.length)];
  for (let n = 1; n < 2000; n++) { const c = hslHex((n * 137.508) % 360, 62 + (n % 3) * 8, 42 + (n % 4) * 5); if (!used.has(c)) return c; }
  return '#8892a6';
}
function upsertMe(){
  if (!me.name || !board) return;
  let m = members.get(me.id);
  if (!m) m = { uid: me.id, name: me.name, col: pickColor(), j: Date.now(), v: 1 };
  else if (m.name !== me.name) m = Object.assign({}, m, { name: me.name, v: m.v + 1 });
  else { fixClashes(); return; }
  members.set(me.id, m); send('mem', [m]); saveSoon(); presenceSet({ name: me.name, col: m.col });
  fixClashes(); renderPeople(); dirty();
}
// Whoever joined the board later gives way: they take a fresh colour, and are asked for another name.
function fixClashes(){
  const mine = members.get(me.id); if (!mine) return;
  const earlier = o => o.uid !== me.id && (o.j < mine.j || (o.j === mine.j && o.uid < mine.uid));
  if ([...members.values()].some(o => earlier(o) && o.col === mine.col)) {
    const n = Object.assign({}, mine, { col: pickColor(), v: mine.v + 1 });
    members.set(me.id, n); send('mem', [n]); saveSoon(); presenceSet({ col: n.col }); renderPeople(); dirty();
  }
  const dup = [...members.values()].find(o => earlier(o) && o.name.trim().toLowerCase() === mine.name.trim().toLowerCase());
  if (dup && $('#joinScrim').hidden) openJoin('Someone on this board is already called ' + dup.name + '. Pick a different name so people can tell you apart.');
}
function applyMem(m){
  if (!m || typeof m.uid !== 'string' || !UID_RE.test(m.uid) || typeof m.name !== 'string' || typeof m.col !== 'string' || !/^#[0-9a-f]{6}$/i.test(m.col) || !num(m.j) || !num(m.v)) return false;
  const cur = members.get(m.uid); if (cur && cur.v >= m.v) return false;
  const n = { uid: m.uid, name: m.name.slice(0, 24), col: m.col.toLowerCase(), j: m.j, v: m.v };
  members.set(m.uid, n);
  if (m.uid === me.id && n.name !== me.name) { me.name = n.name; store.set('fmwb:name', n.name); }
  return true;
}
function applyRec(r){
  if (!r || typeof r.id !== 'string' || !/^[a-z0-9]{4,24}$/.test(r.id) || !num(r.v) || typeof r.by !== 'string') return false;
  const cur = recs.get(r.id);
  if (cur && (cur.v > r.v || (cur.v === r.v && cur.by >= r.by))) return false;
  let o = null;
  if (r.o) { o = clean(r.o); if (!o || o.id !== r.id) return false; }
  clock = Math.max(clock, r.v);
  recs.set(r.id, { id: r.id, o, v: r.v, by: r.by.slice(0, 24) });
  if (o) objs.set(o.id, o); else { objs.delete(r.id); selection.delete(r.id); }
  dropDraftFor(r.id); orderDirty = true;
  return true;
}
function commitRec(id, o){
  clock += 1;
  const r = { id, o: o || null, v: clock, by: me.id };
  recs.set(id, r); sendRecs([r]); saveSoon();
}
function sendRecs(list, target){
  let batch = [], size = 0;
  for (const r of list) {
    const s = r.o && r.o.src ? r.o.src.length + 400 : JSON.stringify(r).length;
    if (batch.length && (size + s > 400000 || batch.length >= 300)) { send('recs', batch, target); batch = []; size = 0; }
    batch.push(r); size += s;
  }
  if (batch.length) send('recs', batch, target);
}
function send(kind, data, target){
  const a = S.act[kind];
  if (a) {
    const pid = target ? tab2peer.get(target) : null;
    if (!target || pid) { try { const p = a.send({ t: TAB, d: data }, pid ? { target: pid } : undefined); if (p && p.catch) p.catch(() => {}); } catch(e) {} }
  }
  if (S.relay) {
    if (kind === 'pres' && !target) relayPres();
    else { try { S.relay.send(kind, data, target || null).catch(() => {}); } catch(e) {} }
  }
  if (!target && S.bc && (kind === 'recs' || kind === 'mem' || kind === 'meta')) { try { S.bc.postMessage({ k: kind, d: data }); } catch(e) {} }
}
// The relay carries cursors a little less often, to stay well inside the public brokers' limits.
let relayPresT = 0, relayPresTimer = 0;
function relayPres(){
  const wait = 150 - (performance.now() - relayPresT);
  if (wait <= 0) { relayPresT = performance.now(); if (S.relay) S.relay.send('pres', presPayload(), null).catch(() => {}); }
  else if (!relayPresTimer) relayPresTimer = setTimeout(() => { relayPresTimer = 0; relayPres(); }, wait);
}
function emit(topic, data){ if (S.room || S.relay) send(topic, data); }
function presPayload(){ return Object.assign({ uid: me.id, name: me.name }, presState); }

let presTimer = 0;
function presenceSet(patch){
  for (const [k, v] of Object.entries(patch)) { if (v === null) delete presState[k]; else presState[k] = v; }
  if (presTimer) return;
  presTimer = setTimeout(() => { presTimer = 0; if (S.room || S.relay) send('pres', presPayload()); }, 70);
}
let viewTimer = 0;
function sendView(){
  if (viewTimer) return;
  viewTimer = setTimeout(() => { viewTimer = 0; const c = toWorld(W / 2, H / 2); presenceSet({ v:[r1(c.x), r1(c.y), r3(cam.z), Math.round(W), Math.round(H)] }); }, 150);
  saveViewSoon();
}
function dropDraftFor(id){ for (const k of drafts.keys()) if (k.endsWith(':' + id)) drafts.delete(k); }

/* --- receiving --- */
function onRecs(list){
  if (!Array.isArray(list)) return; let ch = false;
  for (const r of list.slice(0, 2000)) if (applyRec(r)) ch = true;
  if (ch) { saveSoon(); dirty(); if (tool === 'select') renderProps(); }
}
function onMem(list){
  if (!Array.isArray(list)) return; let ch = false;
  for (const m of list.slice(0, 500)) if (applyMem(m)) ch = true;
  if (ch) { saveSoon(); fixClashes(); rebuildPeers(); }
}
function onMeta(m){
  if (!m || typeof m !== 'object' || typeof m.name !== 'string' || !num(m.v) || typeof m.by !== 'string') return;
  if (m.v < meta.v || (m.v === meta.v && m.by <= meta.by)) return;
  meta = { name: m.name.slice(0, 40), v: m.v, by: m.by.slice(0, 24) }; showBoardName(); rememberBoard(); saveSoon();
}
function onPres(p, peerId){
  if (!p || typeof p.uid !== 'string' || !UID_RE.test(p.uid)) return;
  try { if (JSON.stringify(p).length > 8000) return; } catch(e) { return; }
  if (typeof p.name === 'string') p.name = p.name.slice(0, 24);
  pres.set(peerId, { uid: p.uid, p, t: performance.now() });
  if (p.uid !== me.id && p.las && Array.isArray(p.cur) && num(p.cur[0]) && num(p.cur[1])) {
    let tr = trails.get(peerId); if (!tr) { tr = { col:'#ff3b30', pts:[] }; trails.set(peerId, tr); }
    const l = tr.pts[tr.pts.length - 1];
    if (!l || l.x !== p.cur[0] || l.y !== p.cur[1]) tr.pts.push({ x:p.cur[0], y:p.cur[1], t:performance.now() });
  }
  rebuildPeers();
}
function onMv(d){
  if (!d || !Array.isArray(d.it)) return;
  for (const it of d.it) {
    if (!Array.isArray(it) || typeof it[0] !== 'string' || !num(it[1]) || !num(it[2])) continue;
    const o = objs.get(it[0]); if (!o) continue;
    const n = Object.assign({}, o, { x: it[1], y: it[2] });
    if (num(it[3]) && num(it[4]) && n.w) { n.w = Math.max(1, it[3]); n.h = Math.max(1, it[4]); }
    if (num(it[5]) && n.t === 'text') n.fs = clamp(it[5], 1, 2000);
    objs.set(n.id, n);
  }
  dirty();
}
function onInk(d, peerId){
  if (!d || typeof d.sid !== 'string' || !Array.isArray(d.p) || !num(d.i) || d.i < 0 || d.i > 12000) return;
  if (objs.has(d.sid)) return;
  const k = peerId + ':' + d.sid; let cur = drafts.get(k);
  if (!cur) { const o = clean({ id:d.sid, t:'stroke', x:d.x, y:d.y, p:d.p.length >= 2 ? d.p.slice(0, 2) : [0,0], c:d.c, sw:d.sw, hl:d.hl }); if (!o) return; o.p = []; cur = { o, last:0 }; }
  if (!d.p.every(num) || cur.o.p.length > 24000) return;
  const p = cur.o.p.slice(); for (let j = 0; j < d.p.length; j++) p[d.i * 2 + j] = d.p[j];
  for (let j = 0; j < p.length; j++) if (p[j] === undefined) p[j] = p[j - 2] !== undefined ? p[j - 2] : 0;
  cur.o = Object.assign({}, cur.o, { p }); cur.last = performance.now(); drafts.set(k, cur); overlay();
}
function digest(){ const out = []; for (const r of recs.values()) out.push([r.id, r.v, r.by]); return out; }
function onSum(list, peerId){
  if (!Array.isArray(list) || list.length > 50000) return;
  const theirs = new Map();
  for (const e of list) if (Array.isArray(e) && typeof e[0] === 'string') theirs.set(e[0], e);
  const out = [];
  for (const r of recs.values()) { const t = theirs.get(r.id); if (!t || t[1] < r.v || (t[1] === r.v && t[2] < r.by)) out.push(r); }
  if (out.length) sendRecs(out, peerId);
}
function greet(tab){
  send('mem', [...members.values()], tab);
  if (meta.v) send('meta', meta, tab);
  send('sum', digest(), tab);
  send('pres', presPayload(), tab);
}
function recv(kind, d, tab){
  if (typeof tab !== 'string' || !TAB_RE.test(tab) || tab === TAB) return;
  if (kind === 'bye') { dropTab(tab); return; }
  if (!known.has(tab)) { known.add(tab); greet(tab); }
  switch (kind) {
    case 'recs': onRecs(d); break;
    case 'mem': onMem(d); break;
    case 'meta': onMeta(d); break;
    case 'sum': onSum(d, tab); break;
    case 'pres': onPres(d, tab); break;
    case 'mv': onMv(d); break;
    case 'ink': onInk(d, tab); break;
  }
}
function dropTab(tab){
  pres.delete(tab); trails.delete(tab); curDisp.delete(tab); known.delete(tab);
  for (const k of drafts.keys()) if (k.startsWith(tab + ':')) drafts.delete(k);
  if (followPeer === tab) stopFollow(true);
  rebuildPeers();
}
// Heartbeat: keep everyone's people list fresh, and drop anyone silent for 15 s.
setInterval(() => {
  if (!S.open) return;
  if (S.room || S.relayUp) send('pres', presPayload());
  const now = performance.now();
  for (const [tab, e] of [...pres]) if (now - e.t > 15000) dropTab(tab);
  updateStatus();
}, 4000);
function rebuildPeers(){
  const primary = new Map();
  for (const [peer, e] of pres) { if (e.uid === me.id) continue; const q = primary.get(e.uid); if (!q || e.t > q.t) primary.set(e.uid, { peer, t: e.t }); }
  peers = [];
  for (const [peer, e] of pres) {
    if (e.uid === me.id) continue;
    const m = members.get(e.uid);
    peers.push({ peer, uid: e.uid, isMe:false, sameTab:false, kind:'viewer', guest:false, primary: primary.get(e.uid).peer === peer,
      presence: Object.assign({}, e.p, { col: (m && m.col) || e.p.col, name: (m && m.name) || e.p.name }) });
  }
  renderPeople(); updateStatus(); overlay();
}

/* --- storage on this device --- */
let dbp = null;
function idb(){
  if (!dbp) dbp = new Promise((res, rej) => { const r = indexedDB.open('fmwb', 1); r.onupgradeneeded = () => r.result.createObjectStore('boards'); r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
  return dbp;
}
async function idbGet(k){ try { const d = await idb(); return await new Promise(res => { const q = d.transaction('boards').objectStore('boards').get(k); q.onsuccess = () => res(q.result || null); q.onerror = () => res(null); }); } catch(e) { return null; } }
async function idbPut(k, v){ try { const d = await idb(); d.transaction('boards', 'readwrite').objectStore('boards').put(v, k); } catch(e) {} }
let saveT = 0;
function saveSoon(){ clearTimeout(saveT); saveT = setTimeout(saveNow, 700); }
function saveNow(){ clearTimeout(saveT); if (!board || !S.open) return; idbPut(board, { recs:[...recs.values()], mem:[...members.values()], meta, clock }); }
window.addEventListener('pagehide', () => { if (S.room || S.relay) send('bye', 1); saveNow(); saveViewNow(); });
document.addEventListener('visibilitychange', () => { if (document.hidden) { saveNow(); saveViewNow(); } });

function boardsList(){ try { const a = JSON.parse(store.get('fmwb:boards') || '[]'); return Array.isArray(a) ? a.filter(b => b && /^[a-z0-9]{8,24}$/.test(b.code)) : []; } catch(e) { return []; } }
function rememberBoard(){
  if (!board) return;
  const list = boardsList().filter(b => b.code !== board);
  list.unshift({ code: board, name: meta.name || '', last: Date.now() });
  store.set('fmwb:boards', JSON.stringify(list.slice(0, 50))); store.set('fmwb:last', board);
}
function showBoardName(){ $('#boardName').textContent = meta.name || 'Untitled board'; document.title = (meta.name ? meta.name + ' · ' : '') + 'Further Maths Board'; }

/* --- per-board view, so reopening the link puts you back where you were --- */
let viewSaveT = 0;
function viewState(){ return { cam:{ x:cam.x, y:cam.y, z:cam.z }, tool, ink:prefs.ink, hl:prefs.hl, size:prefs.size, hlSize:prefs.hlSize, dash:prefs.dash, calc: !$('#calc').hidden }; }
function saveViewSoon(){ if (!board || !S.open) return; clearTimeout(viewSaveT); viewSaveT = setTimeout(saveViewNow, 400); }
function saveViewNow(){ clearTimeout(viewSaveT); if (!board || !S.open) return; store.set('fmwb:view:' + board, JSON.stringify(viewState())); }
function restoreView(){
  let v = null; try { v = JSON.parse(store.get('fmwb:view:' + board) || 'null'); } catch(e) {}
  if (v && v.cam && [v.cam.x, v.cam.y, v.cam.z].every(num)) { cam.x = v.cam.x; cam.y = v.cam.y; cam.z = clamp(v.cam.z, 0.04, 24); camChanged(); }
  else centerOn(0, 0, 1);
  if (v) {
    if (INK[v.ink]) prefs.ink = v.ink; if (HL[v.hl]) prefs.hl = v.hl;
    if ([0,1,2].includes(v.size)) prefs.size = v.size; if ([0,1,2].includes(v.hlSize)) prefs.hlSize = v.hlSize;
    prefs.dash = !!v.dash;
  }
  const tools = Object.values(KEYTOOLS);
  setTool(v && tools.includes(v.tool) ? v.tool : 'pen');
  toggleCalc(!!(v && v.calc), true);
}

/* --- opening a board --- */
function leaveBoard(){
  if (S.open) { saveNow(); saveViewNow(); }
  S.token++;
  if (S.room || S.relay) send('bye', 1);
  if (S.room) { try { S.room.leave(); } catch(e) {} }
  if (S.relay) { const r = S.relay; setTimeout(() => r.close(), 300); }
  S.room = null; S.act = {}; S.relay = null; S.relayUp = 0;
  peer2tab.clear(); tab2peer.clear(); known.clear(); curDisp.clear();
  if (S.bc) { try { S.bc.close(); } catch(e) {} S.bc = null; }
  S.open = false;
}
let pendingName = null;
async function openBoard(code){
  if (editing) commitText();
  closeGraph();
  leaveBoard();
  const token = S.token;
  board = code;
  objs.clear(); recs.clear(); members.clear(); pres.clear(); drafts.clear(); trails.clear(); known.clear(); curDisp.clear();
  orderDirty = true; peers = []; selection.clear(); undoStack = []; redoStack = []; followPeer = null; clock = 0; presState = {};
  meta = { name:'', v:0, by:'' };
  updateHist(); renderProps(); renderPeople(); showBoardName(); dirty();
  const saved = await idbGet(code);
  if (token !== S.token) return;
  if (saved) {
    for (const m of saved.mem || []) applyMem(m);
    for (const r of saved.recs || []) applyRec(r);
    if (saved.meta) onMeta(saved.meta);
    if (num(saved.clock)) clock = Math.max(clock, saved.clock);
  }
  if (pendingName && pendingName.code === code && !meta.v) { meta = { name: pendingName.name, v: 1, by: me.id }; }
  pendingName = null;
  S.open = true;
  showBoardName(); rememberBoard(); restoreView();
  presenceSet({ name: me.name, tool });
  upsertMe();
  orderDirty = true; dirty(); updateStatus();
  try {
    S.bc = new BroadcastChannel('fmwb-' + code);
    S.bc.onmessage = ev => { const m = ev.data || {}; if (m.k === 'recs') onRecs(m.d); else if (m.k === 'mem') onMem(m.d); else if (m.k === 'meta') onMeta(m.d); };
  } catch(e) { S.bc = null; }
  joinNet(token);
}
async function joinNet(token){
  S.netStart = performance.now(); updateStatus();
  setTimeout(() => { if (token === S.token) updateStatus(); }, 12500);
  // 1. Encrypted relay through public brokers: works on every network, including mobile data.
  if (window.FMRelay && window.crypto && crypto.subtle) {
    FMRelay.create(board, TAB,
      (k, d, from, to) => { if (token === S.token && (!to || to === TAB)) recv(k, d, from); },
      up => { if (token !== S.token) return; const was = S.relayUp; S.relayUp = up; if (up && !was) { send('pres', presPayload()); if (me.name) send('mem', [...members.values()]); } updateStatus(); })
      .then(r => { if (token !== S.token) r.close(); else S.relay = r; })
      .catch(() => {});
  }
  // 2. Direct browser-to-browser connections: fastest when the network allows them.
  try { if (!S.lib) S.lib = await import(LIB_URL); } catch(e) { S.lib = null; }
  if (token !== S.token || !S.lib) { updateStatus(); return; }
  let room = null;
  try { room = S.lib.joinRoom({ appId: APP_ID, password: 'fmwb-' + board }, 'board-' + board, { onJoinError: () => {} }); } catch(e) { room = null; }
  if (!room) { updateStatus(); return; }
  S.room = room;
  for (const n of ['recs', 'mem', 'meta', 'sum', 'pres', 'mv', 'ink', 'bye']) {
    const a = room.makeAction(n);
    a.onMessage = (m, info) => {
      if (token !== S.token || !m || typeof m.t !== 'string' || !TAB_RE.test(m.t)) return;
      const pid = info && info.peerId; if (pid) { peer2tab.set(pid, m.t); tab2peer.set(m.t, pid); }
      recv(n, m.d, m.t);
    };
    S.act[n] = a;
  }
  room.onPeerJoin = pid => { if (token !== S.token) return; try { const pr = S.act.pres.send({ t: TAB, d: presPayload() }, { target: pid }); if (pr && pr.catch) pr.catch(() => {}); } catch(e) {} };
  room.onPeerLeave = pid => { if (token !== S.token) return; const tab = peer2tab.get(pid); peer2tab.delete(pid); if (tab && tab2peer.get(tab) === pid) tab2peer.delete(tab); };
  updateStatus();
  send('pres', presPayload());
  if (me.name) send('mem', [...members.values()]);
}

function updateStatus(){
  const el = $('#status'), t = el.querySelector('.txt');
  const others = new Set(peers.map(p => p.uid)).size;
  const linked = !!S.room || S.relayUp > 0;
  el.classList.remove('live', 'warn');
  let txt, tip;
  if (others) { el.classList.add('live'); txt = `Live · ${others + 1} here`; tip = 'Everyone here sees changes as they happen. The board is also saved on this device.'; }
  else if (linked) { el.classList.add('live'); txt = 'Live · waiting for friends'; tip = 'Connected. Send the Invite link and people will appear here.'; }
  else if (performance.now() - S.netStart < 12000) { txt = 'Connecting…'; tip = 'Looking for others on this board.'; }
  else { el.classList.add('warn'); txt = 'Offline · saved here'; tip = 'You can keep working. It saves on this device and syncs when you are back online.'; }
  t.textContent = txt; el.title = tip;
}

/* --- home screen + routing --- */
function newCode(){ let s = ''; while (s.length < 10) s += Math.random().toString(36).slice(2); return s.slice(0, 10); }
function showHome(){
  if (S.open) leaveBoard();
  board = null; objs.clear(); orderDirty = true; peers = []; renderPeople(); dirty();
  $('#home').hidden = false; $('#homeName').textContent = me.name || 'no name yet';
  const ul = $('#boardList'); ul.textContent = '';
  const list = boardsList();
  if (!list.length) ul.appendChild(elt('li', { class:'emptyb', text:'No boards yet. Make one above, then press Invite to send the link to your group.' }));
  for (const b of list) {
    const when = new Date(b.last || Date.now());
    ul.appendChild(elt('li', {}, [elt('a', { href:'#' + b.code }, [elt('span', { class:'bname', text: b.name || 'Untitled board' }), elt('span', { class:'bwhen', text: when.toLocaleDateString(undefined, { day:'numeric', month:'short' }) + ' ' + when.toLocaleTimeString(undefined, { hour:'2-digit', minute:'2-digit' }) })])]));
  }
  if (!me.name) openJoin();
}
function route(){
  const h = (location.hash || '').slice(1).toLowerCase();
  if (/^[a-z0-9]{8,24}$/.test(h)) {
    $('#home').hidden = true;
    if (h !== board || !S.open) openBoard(h);
    if (!me.name) openJoin();
    return;
  }
  if (h === '') { const last = store.get('fmwb:last'); if (last && /^[a-z0-9]{8,24}$/.test(last)) { location.replace('#' + last); return; } }
  showHome();
}
window.addEventListener('hashchange', route);
$('#newForm').addEventListener('submit', e => {
  e.preventDefault();
  const name = $('#newName').value.trim().slice(0, 40) || 'Untitled board';
  const code = newCode(); pendingName = { code, name }; $('#newName').value = '';
  location.hash = code;
});
$('#homeRename').addEventListener('click', () => openJoin());
// Keep tabs of the same browser in step when the name changes in another tab.
window.addEventListener('storage', e => {
  if (e.key === 'fmwb:name' && e.newValue && e.newValue !== me.name) { me.name = e.newValue; $('#homeName').textContent = me.name; if (S.open) upsertMe(); renderPeople(); }
});

/* ---------------- mutations (+ undo) ---------------- */
function writeObj(o){
  objs.set(o.id, o); orderDirty = true; dirty();
  if (JSON.stringify(o).length > 300000) { toast('That item is too big to share.'); return; }
  commitRec(o.id, o);
}
function addObjects(list, record = true){
  for (const o of list) writeObj(o);
  if (record) pushUndo({ k:'add', objs:list.map(o => o) });
}
function deleteObjects(ids, record = true){
  const gone = [];
  for (const id of ids) { const o = objs.get(id); if (!o) continue; gone.push(o); objs.delete(id); selection.delete(id); commitRec(id, null); }
  if (!gone.length) return;
  orderDirty = true; dirty();
  if (record) pushUndo({ k:'del', objs:gone });
  renderProps();
}
function replaceObjects(pairs, record = true){ // pairs: [before, after]
  for (const [, a] of pairs) writeObj(a);
  if (record) pushUndo({ k:'rep', pairs });
}
function emitMoves(list){
  for (let i = 0; i < list.length; i += 120)
    emit('mv', { it: list.slice(i, i + 120).map(o => [o.id, r1(o.x), r1(o.y), o.w ? r1(o.w) : null, o.h ? r1(o.h) : null, o.t === 'text' ? r3(o.fs) : null]) });
}
function pushUndo(op){ undoStack.push(op); if (undoStack.length > 200) undoStack.shift(); redoStack = []; updateHist(); }
function invert(op){
  if (op.k === 'add') return { k:'del', objs:op.objs };
  if (op.k === 'del') return { k:'add', objs:op.objs };
  return { k:'rep', pairs:op.pairs.map(([b, a]) => [a, b]) };
}
function applyOp(op){
  if (op.k === 'add') addObjects(op.objs, false);
  else if (op.k === 'del') deleteObjects(op.objs.map(o => o.id), false);
  else replaceObjects(op.pairs, false);
}
function undo(){ const op = undoStack.pop(); if (!op) return; applyOp(invert(op)); redoStack.push(op); updateHist(); renderProps(); }
function redo(){ const op = redoStack.pop(); if (!op) return; applyOp(op); undoStack.push(op); updateHist(); renderProps(); }
function updateHist(){ $('#undoBtn').disabled = !undoStack.length; $('#redoBtn').disabled = !redoStack.length; }
const newZ = () => Date.now() + Math.random();

/* ---------------- pointer input ---------------- */
const pointers = new Map();
let inkTimer = 0, inkSent = 0;
function evPos(e){ return { sx: e.clientX - rect.left, sy: e.clientY - rect.top }; }
function remeasure(){ rect = cv.getBoundingClientRect(); }
// Phones can leave the page nudged after the on-screen keyboard closes; snap it back and re-measure.
function unNudge(){ if (window.scrollX || window.scrollY) window.scrollTo(0, 0); remeasure(); }
window.addEventListener('scroll', unNudge, { passive:true });
if (window.visualViewport) { visualViewport.addEventListener('resize', unNudge); visualViewport.addEventListener('scroll', unNudge); }
function setCursorClass(){
  cv.className = 't-' + tool + (spaceDown ? ' panning' : '') + (gesture && gesture.mode === 'pan' ? ' grabbing' : '');
}

let penDown = false, penUpAt = 0;
cv.addEventListener('pointerdown', e => {
  const before = gesture;
  onDown(e);
  if (gesture && gesture !== before && gesture.mode !== 'pinch') { gesture.pid = e.pointerId; gesture.touch = e.pointerType === 'touch'; }
});
function onDown(e){
  remeasure();
  if (editing) commitText();
  closeMenus();
  if (e.pointerType === 'pen') {
    penDown = true;
    if (!prefs.fingerPans && store.get('fmwb:fpAuto') !== '1') {
      prefs.fingerPans = true; store.set('fmwb:fp', '1'); store.set('fmwb:fpAuto', '1');
      toast('Stylus found: your pen writes, fingers move and zoom the board. You can change this in the ⋯ menu.', 5000);
    }
    // A palm that landed just before the pen: undo whatever it started.
    if (gesture && gesture.touch) {
      if (gesture.mode === 'pan') { cam.x = gesture.cx; cam.y = gesture.cy; camChanged(); }
      else if (gesture.mode === 'pinch' && gesture.cam0) { Object.assign(cam, gesture.cam0); camChanged(); }
      if (gesture.mode === 'draw') { draft = null; stopInk(); }
      else if (gesture.mode === 'shape') { draft = null; presenceSet({ dr:null }); }
      gesture = null; dirty();
    }
    for (const [id, q] of pointers) if (q.type === 'touch') pointers.delete(id);
  } else if (e.pointerType === 'touch' && (penDown || performance.now() - penUpAt < 600)) {
    return; // palm resting on the screen while writing
  }
  const { sx, sy } = evPos(e);
  pointers.set(e.pointerId, { sx, sy, type:e.pointerType });
  try { cv.setPointerCapture(e.pointerId); } catch(err) {}
  const touches = [...pointers.values()].filter(p => p.type === 'touch');
  if (e.pointerType === 'touch' && touches.length === 2) {
    cancelGesture();
    const [a, b] = touches; const mid = { sx:(a.sx + b.sx) / 2, sy:(a.sy + b.sy) / 2 };
    gesture = { mode:'pinch', touch:true, d0: Math.hypot(a.sx - b.sx, a.sy - b.sy) || 1, z0: cam.z, w0: toWorld(mid.sx, mid.sy), cam0:{ x:cam.x, y:cam.y, z:cam.z } };
    stopFollow(true); return;
  }
  if (gesture) return;
  const w = toWorld(sx, sy); lastWorld = w;
  const wantsPan = e.button === 1 || e.button === 2 || spaceDown || tool === 'hand' || (e.pointerType === 'touch' && prefs.fingerPans && tool !== 'select');
  if (wantsPan) { gesture = { mode:'pan', sx, sy, cx:cam.x, cy:cam.y }; stopFollow(); setCursorClass(); return; }
  if (e.button !== 0 && e.pointerType === 'mouse') return;
  const tol = 6 / cam.z;
  switch (tool) {
    case 'pen': case 'marker': {
      const hl = tool === 'marker';
      draft = { id: rid(), t:'stroke', x: r1(w.x), y: r1(w.y), p:[0, 0], c: hl ? prefs.hl : prefs.ink, sw: r3((hl ? HL_SIZES[prefs.hlSize] : PEN_SIZES[prefs.size]) / cam.z), hl, z: newZ(), by: me.name };
      gesture = { mode:'draw' }; inkSent = 0; startInk(); dirty(); break; }
    case 'eraser': gesture = { mode:'erase', gone:[] }; eraseAt(w, gesture); break;
    case 'laser': gesture = { mode:'laser' }; laserPoint(w); break;
    case 'line': case 'arrow': case 'rect': case 'ellipse': case 'axes':
      gesture = { mode:'shape', x0:w.x, y0:w.y }; break;
    case 'text': {
      const t = topHit(w, tol, o => o.t === 'text');
      if (t) openTextEditor(t, false);
      else openTextEditor({ id: rid(), t:'text', x: r1(w.x), y: r1(w.y - 13 / cam.z), s:'', c: prefs.ink, fs: r3(22 / cam.z), z: newZ(), by: me.name }, true);
      e.preventDefault(); break; }
    case 'graph': {
      const gw = 380 / cam.z, gh = 300 / cam.z;
      const o = { id: rid(), t:'graph', x: r1(w.x), y: r1(w.y), w: r1(gw), h: r1(gh), sw: 1, fx:['x^3 - 3x', '', '', ''], xa:-4, xb:4, ya:-5, yb:5, c:'ink', z:newZ(), by: me.name };
      addObjects([o]); setTool('select'); selection.clear(); selection.add(o.id); renderProps(); openGraphEditor(o.id); break; }
    case 'select': {
      const hb = handleBox();
      if (hb && w.x >= hb[0] - tol && w.x <= hb[0] + hb[2] + tol && w.y >= hb[1] - tol && w.y <= hb[1] + hb[2] + tol) {
        const o = objs.get([...selection][0]); const b = bbox(o);
        gesture = { mode:'resize', o, bw: b[2] - b[0], bh: b[3] - b[1], x0: w.x, y0: w.y }; break;
      }
      const o = topHit(w, tol);
      if (o) {
        if (e.shiftKey) { selection.has(o.id) ? selection.delete(o.id) : selection.add(o.id); }
        else if (!selection.has(o.id)) { selection.clear(); selection.add(o.id); }
        const orig = [...selection].map(id => objs.get(id)).filter(Boolean);
        gesture = { mode:'move', x0:w.x, y0:w.y, orig, moved:false, lastEmit:0 };
        if (e.pointerType !== 'mouse' && isDoubleTap(o.id)) { gesture = null; editObject(o); }
      } else {
        if (!e.shiftKey) selection.clear();
        gesture = { mode:'marquee', x0:w.x, y0:w.y, x1:w.x, y1:w.y, base: new Set(selection) };
      }
      renderProps(); dirty(); break; }
  }
}
let lastTap = { id:null, t:0 };
function isDoubleTap(id){ const now = Date.now(), ok = lastTap.id === id && now - lastTap.t < 380; lastTap = { id, t: now }; return ok; }
cv.addEventListener('dblclick', e => {
  if (tool !== 'select') return;
  const { sx, sy } = evPos(e); const o = topHit(toWorld(sx, sy), 6 / cam.z); if (o) editObject(o);
});
function editObject(o){
  if (o.t === 'text') { openTextEditor(o, false); }
  else if (o.t === 'graph') { openGraphEditor(o.id); }
}
cv.addEventListener('contextmenu', e => e.preventDefault());
['gesturestart','gesturechange','gestureend'].forEach(n => document.addEventListener(n, e => e.preventDefault()));
document.addEventListener('dblclick', e => { if (!e.target.closest('input,textarea')) e.preventDefault(); });

function topHit(w, tol, filter){
  const arr = sortedObjs();
  for (let i = arr.length - 1; i >= 0; i--) { const o = arr[i]; if (filter && !filter(o)) continue; if (hit(o, w.x, w.y, tol, false)) return o; }
  return null;
}

cv.addEventListener('pointermove', e => {
  if (e.pointerType === 'touch' && !pointers.has(e.pointerId)) return;
  const { sx, sy } = evPos(e);
  const pp = pointers.get(e.pointerId); if (pp) { pp.sx = sx; pp.sy = sy; }
  const w = toWorld(sx, sy); lastWorld = w;
  if (e.pointerType !== 'touch' || gesture) presenceSet({ cur:[r1(w.x), r1(w.y)] });
  if (tool === 'eraser') overlay();
  if (!gesture) return;
  const g = gesture;
  if (g.mode !== 'pinch' && g.pid !== undefined && g.pid !== e.pointerId) return;
  switch (g.mode) {
    case 'pinch': {
      const ts = [...pointers.values()].filter(p => p.type === 'touch'); if (ts.length < 2) return;
      const [a, b] = ts; const mid = { sx:(a.sx + b.sx) / 2, sy:(a.sy + b.sy) / 2 };
      const nz = clamp(g.z0 * Math.hypot(a.sx - b.sx, a.sy - b.sy) / g.d0, 0.04, 24);
      cam.z = nz; cam.x = g.w0.x - mid.sx / nz; cam.y = g.w0.y - mid.sy / nz; camChanged(); break; }
    case 'pan': cam.x = g.cx - (sx - g.sx) / cam.z; cam.y = g.cy - (sy - g.sy) / cam.z; camChanged(); break;
    case 'draw': {
      const evs = e.getCoalescedEvents ? e.getCoalescedEvents() : [e];
      const minD = 1.1 / cam.z;
      for (const ev of (evs.length ? evs : [e])) {
        const q = toWorld(ev.clientX - rect.left, ev.clientY - rect.top);
        const px = r1(q.x - draft.x), py = r1(q.y - draft.y), p = draft.p;
        if (Math.hypot(px - p[p.length - 2], py - p[p.length - 1]) < minD) continue;
        p.push(px, py);
      }
      if (draft.p.length > 20000) finishStroke();
      overlay(); break; }
    case 'erase': eraseAt(w, g); break;
    case 'laser': laserPoint(w); break;
    case 'shape': {
      let x1 = w.x, y1 = w.y; const dx = x1 - g.x0, dy = y1 - g.y0;
      const sw = r3(PEN_SIZES[prefs.size] / cam.z);
      if (tool === 'line' || tool === 'arrow') {
        let ex = dx, ey = dy;
        if (e.shiftKey) { const L = Math.hypot(dx, dy), a = Math.round(Math.atan2(dy, dx) / (Math.PI / 12)) * (Math.PI / 12); ex = L * Math.cos(a); ey = L * Math.sin(a); }
        draft = { id:'draft', t:'line', x: r1(g.x0), y: r1(g.y0), ex: r1(ex), ey: r1(ey), sw, a: tool === 'arrow', d: prefs.dash, c: prefs.ink, z:0 };
      } else {
        let wd = dx, ht = dy;
        if (e.shiftKey) { const m = Math.max(Math.abs(wd), Math.abs(ht)); wd = Math.sign(wd || 1) * m; ht = Math.sign(ht || 1) * m; }
        const x = Math.min(g.x0, g.x0 + wd), y = Math.min(g.y0, g.y0 + ht);
        draft = { id:'draft', t: tool, x: r1(x), y: r1(y), w: r1(Math.max(Math.abs(wd), 0.1)), h: r1(Math.max(Math.abs(ht), 0.1)), sw, d: tool !== 'axes' && prefs.dash, c: prefs.ink, z:0 };
      }
      const dr = Object.assign({}, draft); delete dr.id; presenceSet({ dr });
      overlay(); break; }
    case 'move': {
      const dx = w.x - g.x0, dy = w.y - g.y0; g.moved = g.moved || Math.hypot(dx, dy) * cam.z > 2;
      if (!g.moved) return;
      g.cur = g.orig.map(o => moveObj(o, dx, dy));
      for (const o of g.cur) objs.set(o.id, o);
      const now = performance.now(); if (now - g.lastEmit > 120) { g.lastEmit = now; emitMoves(g.cur); }
      dirty(); break; }
    case 'resize': {
      const o = g.o; let n;
      const nw = Math.max(12 / cam.z, g.bw + (w.x - g.x0)), nh = Math.max(12 / cam.z, g.bh + (w.y - g.y0));
      if (o.t === 'text') { n = Object.assign({}, o, { fs: r3(clamp(o.fs * nw / g.bw, 1, 2000)) }); }
      else if (o.t === 'image') { const k = nw / g.bw; n = Object.assign({}, o, { w: r1(o.w * k), h: r1(o.h * k) }); }
      else n = Object.assign({}, o, { w: r1(Math.max(4, o.w + (nw - g.bw))), h: r1(Math.max(4, o.h + (nh - g.bh))) });
      g.cur = n; objs.set(n.id, n);
      const now = performance.now(); if (!g.lastEmit || now - g.lastEmit > 120) { g.lastEmit = now; emitMoves([n]); }
      dirty(); break; }
    case 'marquee': {
      g.x1 = w.x; g.y1 = w.y;
      const x0 = Math.min(g.x0, g.x1), x1 = Math.max(g.x0, g.x1), y0 = Math.min(g.y0, g.y1), y1 = Math.max(g.y0, g.y1);
      selection.clear(); g.base.forEach(id => selection.add(id));
      for (const o of objs.values()) { const b = bbox(o); if (b[0] < x1 && b[2] > x0 && b[1] < y1 && b[3] > y0) selection.add(o.id); }
      dirty(); break; }
  }
});
function moveObj(o, dx, dy){ return Object.assign({}, o, { x: r1(o.x + dx), y: r1(o.y + dy) }); }

function endPointer(e){
  pointers.delete(e.pointerId);
  if (e.pointerType === 'pen') { penDown = false; penUpAt = performance.now(); }
  if (!gesture) return;
  const g = gesture;
  if (g.mode === 'pinch') { if (![...pointers.values()].some(p => p.type === 'touch')) gesture = null; return; }
  if (g.pid !== undefined && g.pid !== e.pointerId) return;
  gesture = null;
  switch (g.mode) {
    case 'pan': setCursorClass(); break;
    case 'draw': finishStroke(); break;
    case 'erase': if (g.gone.length) pushUndo({ k:'del', objs:g.gone }); break;
    case 'laser': presenceSet({ las:null }); break;
    case 'shape': {
      const d = draft; draft = null; presenceSet({ dr:null });
      if (!d) break;
      const big = d.t === 'line' ? Math.hypot(d.ex, d.ey) * cam.z > 3 : (d.w * cam.z > 4 || d.h * cam.z > 4);
      if (big) { d.id = rid(); d.z = newZ(); d.by = me.name; addObjects([d]); }
      dirty(); break; }
    case 'move':
      if (g.moved && g.cur) replaceObjects(g.orig.map((o, i) => [o, g.cur[i]]));
      break;
    case 'resize': if (g.cur) replaceObjects([[g.o, g.cur]]); break;
    case 'marquee': renderProps(); dirty(); break;
  }
}
cv.addEventListener('pointerup', endPointer);
cv.addEventListener('pointercancel', e => { if (gesture && gesture.mode === 'draw' && gesture.pid === e.pointerId) { draft = null; stopInk(); gesture = null; dirty(); } endPointer(e); });
cv.addEventListener('pointerleave', e => { if (e.pointerType === 'mouse' && !gesture) { lastWorld = null; presenceSet({ cur:null }); dirty(); } });

function cancelGesture(){
  if (!gesture) return;
  if (gesture.mode === 'draw') { if (draft && draft.p.length > 12) finishStroke(); else { draft = null; stopInk(); } }
  if (gesture.mode === 'shape') { draft = null; presenceSet({ dr:null }); }
  if (gesture.mode === 'move' && gesture.moved && gesture.cur) replaceObjects(gesture.orig.map((o, i) => [o, gesture.cur[i]]));
  gesture = null; dirty();
}
function startInk(){ clearInterval(inkTimer); inkTimer = setInterval(sendInk, 90); }
function stopInk(){ clearInterval(inkTimer); inkTimer = 0; }
function sendInk(){
  if (!draft || draft.t !== 'stroke' || !S.room) return;
  const n = draft.p.length / 2; if (n <= inkSent) return;
  const from = Math.max(0, inkSent), to = Math.min(n, from + 300);
  emit('ink', { sid: draft.id, i: from, p: draft.p.slice(from * 2, to * 2), x: draft.x, y: draft.y, c: draft.c, sw: draft.sw, hl: draft.hl });
  inkSent = to;
}
function finishStroke(){
  stopInk(); const d = draft; draft = null; if (!d) return;
  addObjects([d]); dirty();
}
function eraseAt(w, g){
  const tol = 9 / cam.z, ids = [];
  for (const o of objs.values()) if (ERASABLE.has(o.t) && hit(o, w.x, w.y, tol, true)) ids.push(o.id);
  if (!ids.length) return;
  for (const id of ids) g.gone.push(objs.get(id));
  deleteObjects(ids, false);
}
function laserPoint(w){
  let tr = trails.get('me'); if (!tr) { tr = { col:'#ff3b30', pts:[] }; trails.set('me', tr); }
  tr.pts.push({ x:w.x, y:w.y, t:performance.now() });
  presenceSet({ las:1, cur:[r1(w.x), r1(w.y)] }); overlay();
}

cv.addEventListener('wheel', e => {
  e.preventDefault(); stopFollow(true);
  const { sx, sy } = evPos(e);
  const isMouseWheel = e.deltaMode === 1 || (e.deltaX === 0 && Math.abs(e.deltaY) >= 50 && Number.isInteger(e.deltaY));
  if (e.ctrlKey || e.metaKey || isMouseWheel) {
    const d = e.deltaMode === 1 ? e.deltaY * 33 : e.deltaY;
    zoomAt(sx, sy, cam.z * Math.exp(-clamp(d, -120, 120) * (e.ctrlKey && !isMouseWheel ? 0.012 : 0.0022)));
  } else { cam.x += e.deltaX / cam.z; cam.y += e.deltaY / cam.z; camChanged(); }
}, { passive:false });

/* ---------------- keyboard ---------------- */
const KEYTOOLS = { v:'select', h:'hand', p:'pen', m:'marker', e:'eraser', q:'laser', l:'line', a:'arrow', r:'rect', o:'ellipse', x:'axes', t:'text', g:'graph' };
function typing(){ const a = document.activeElement; return a && (a.tagName === 'INPUT' || a.tagName === 'TEXTAREA' || a.isContentEditable); }
window.addEventListener('keydown', e => {
  if (typing()) { if (e.key === 'Escape') { if (editing) commitText(); else document.activeElement.blur(); } return; }
  const mod = e.ctrlKey || e.metaKey, k = e.key.toLowerCase();
  if (e.code === 'Space') { if (!spaceDown) { spaceDown = true; setCursorClass(); } e.preventDefault(); return; }
  if (mod && k === 'z') { e.preventDefault(); e.shiftKey ? redo() : undo(); return; }
  if (mod && k === 'y') { e.preventDefault(); redo(); return; }
  if (mod && k === 'd') { e.preventDefault(); duplicateSel(); return; }
  if (mod && k === 'a') { e.preventDefault(); setTool('select'); for (const id of objs.keys()) selection.add(id); renderProps(); dirty(); return; }
  if (mod) return;
  if (e.key === 'Delete' || e.key === 'Backspace') { if (selection.size) { e.preventDefault(); deleteObjects([...selection]); } return; }
  if (e.key === 'Escape') { selection.clear(); closeMenus(); renderProps(); dirty(); return; }
  if (e.key === '+' || e.key === '=') { zoomAt(W / 2, H / 2, cam.z * 1.25); return; }
  if (e.key === '-' || e.key === '_') { zoomAt(W / 2, H / 2, cam.z / 1.25); return; }
  if (k === '0') { zoomAt(W / 2, H / 2, 1); return; }
  if (k === 'f') { fitAll(); return; }
  if (k === 'c') { toggleCalc(); return; }
  if (k === 'i') { $('#fileIn').click(); return; }
  if (KEYTOOLS[k]) setTool(KEYTOOLS[k]);
});
window.addEventListener('keyup', e => { if (e.code === 'Space') { spaceDown = false; setCursorClass(); } });
window.addEventListener('blur', () => { spaceDown = false; setCursorClass(); });

/* ---------------- tools + props UI ---------------- */
function setTool(t){
  if (editing && t !== 'text') commitText();
  tool = t; $$('#tools [data-tool]').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.tool === t)));
  if (t !== 'select') selection.clear();
  setCursorClass(); renderProps(); presenceSet({ tool:t }); saveViewSoon(); dirty();
}
$$('#tools [data-tool]').forEach(b => b.addEventListener('click', () => setTool(b.dataset.tool)));

const elt = (tag, attrs = {}, kids = []) => { const n = document.createElement(tag); for (const [k, v] of Object.entries(attrs)) { if (k === 'text') n.textContent = v; else if (k.startsWith('on')) n.addEventListener(k.slice(2), v); else n.setAttribute(k, v); } for (const c of [].concat(kids)) if (c) n.appendChild(c); return n; };
function swatches(keys, current, onPick){
  const g = elt('div', { class:'pgroup', role:'group', 'aria-label':'Colour' });
  for (const k of keys) {
    const b = elt('button', { class:'sw', type:'button', 'aria-pressed': String(k === current), title:k, 'aria-label': k + ' colour', onclick:() => onPick(k) }, [elt('span')]);
    b.firstChild.style.background = colOf(k); g.appendChild(b);
  }
  return g;
}
function sizes(cur, dots, onPick){
  const g = elt('div', { class:'pgroup', role:'group', 'aria-label':'Thickness' });
  dots.forEach((d, i) => { const b = elt('button', { class:'sz', type:'button', 'aria-pressed': String(i === cur), 'aria-label': ['Thin','Medium','Thick'][i], title:['Thin','Medium','Thick'][i], onclick:() => onPick(i) }, [elt('span')]); b.firstChild.style.width = b.firstChild.style.height = d + 'px'; g.appendChild(b); });
  return g;
}
function renderProps(){
  saveViewSoon();
  const P = $('#props'); P.textContent = '';
  const sepE = () => elt('div', { class:'sep' });
  const inkPick = k => { prefs.ink = k; recolorSel(k); renderProps(); };
  if (tool === 'select') {
    if (!selection.size) { P.appendChild(elt('span', { class:'plabel', text:'Click to select · drag empty space to box-select' })); return; }
    const sel = [...selection].map(id => objs.get(id)).filter(Boolean);
    P.appendChild(elt('span', { class:'plabel', text: sel.length + ' selected' }));
    if (sel.some(o => o.t !== 'image' && o.t !== 'graph')) { P.appendChild(swatches(Object.keys(INK), null, inkPick)); P.appendChild(sepE()); }
    if (sel.length === 1 && (sel[0].t === 'text' || sel[0].t === 'graph')) P.appendChild(elt('button', { class:'tiny', type:'button', text:'Edit', onclick:() => editObject(sel[0]) }));
    P.appendChild(elt('button', { class:'tiny', type:'button', text:'Bring to front', onclick:frontSel }));
    P.appendChild(elt('button', { class:'tiny', type:'button', text:'Duplicate', onclick:duplicateSel }));
    P.appendChild(elt('button', { class:'tiny danger', type:'button', text:'Delete', onclick:() => deleteObjects([...selection]) }));
    return;
  }
  if (tool === 'marker') {
    P.appendChild(swatches(Object.keys(HL), prefs.hl, k => { prefs.hl = k; renderProps(); }));
    P.appendChild(sepE()); P.appendChild(sizes(prefs.hlSize, [8, 13, 19], i => { prefs.hlSize = i; renderProps(); }));
    return;
  }
  if (['pen','line','arrow','rect','ellipse','axes','text'].includes(tool)) {
    P.appendChild(swatches(Object.keys(INK), prefs.ink, k => { prefs.ink = k; renderProps(); }));
    if (tool !== 'text') { P.appendChild(sepE()); P.appendChild(sizes(prefs.size, [4, 7, 11], i => { prefs.size = i; renderProps(); })); }
    if (['line','arrow','rect','ellipse'].includes(tool)) { P.appendChild(sepE()); P.appendChild(elt('button', { class:'tiny', type:'button', 'aria-pressed': String(prefs.dash), text:'Dashed', title:'Dashed lines, good for asymptotes', onclick:() => { prefs.dash = !prefs.dash; renderProps(); } })); }
    if (tool === 'line') P.appendChild(elt('span', { class:'plabel', text:'Shift = snap angle' }));
    return;
  }
  const hints = { hand:'Drag to move around · scroll or pinch to zoom', eraser:'Drag over ink to rub it out · images and graphs need Select + Delete', laser:'Point at things for everyone · it fades by itself', graph:'Click on the board to place a graph' };
  P.appendChild(elt('span', { class:'plabel', text: hints[tool] || '' }));
}
function recolorSel(k){
  if (tool !== 'select' || !selection.size) return;
  const pairs = [];
  for (const id of selection) { const o = objs.get(id); if (!o || o.t === 'image' || o.t === 'graph' || o.hl) continue; pairs.push([o, Object.assign({}, o, { c:k })]); }
  if (pairs.length) replaceObjects(pairs);
}
function frontSel(){
  const pairs = [...selection].map(id => objs.get(id)).filter(Boolean).sort((a, b) => a.z - b.z).map((o, i) => [o, Object.assign({}, o, { z: newZ() + i })]);
  if (pairs.length) replaceObjects(pairs);
}
function duplicateSel(){
  const src = [...selection].map(id => objs.get(id)).filter(Boolean); if (!src.length) return;
  const off = 24 / cam.z, copies = src.map((o, i) => Object.assign({}, o, { id: rid(), x: r1(o.x + off), y: r1(o.y + off), z: newZ() + i, by: me.name }));
  addObjects(copies); selection.clear(); copies.forEach(o => selection.add(o.id)); renderProps(); dirty();
}

/* ---------------- text editing ---------------- */
const ta = $('#ta'), symbar = $('#symbar');
const SYMS = ['π','θ','√','∛','²','³','ⁿ','±','×','÷','≤','≥','≠','≈','∞','∫','Σ','∂','Δ','α','β','λ','μ','σ','→','⇒','⇔','∈','ℝ','ℂ','ℤ','°','½','⅓','¼'];
for (const s of SYMS) symbar.appendChild(elt('button', { type:'button', text:s, title:'Insert ' + s, onpointerdown: e => { e.preventDefault(); insertAtCursor(ta, s); sizeEditor(); } }));
function insertAtCursor(input, s){
  const a = input.selectionStart ?? input.value.length, b = input.selectionEnd ?? a;
  input.value = input.value.slice(0, a) + s + input.value.slice(b);
  const p = a + s.length; input.setSelectionRange(p, p); input.focus();
}
function openTextEditor(o, isNew){
  if (editing) commitText();
  editing = { o, isNew };
  ta.value = o.s; ta.hidden = false; symbar.hidden = false;
  positionEditor(); sizeEditor();
  setTimeout(() => { ta.focus(); ta.setSelectionRange(ta.value.length, ta.value.length); }, 0);
  dirty();
}
function positionEditor(){
  if (!editing) return; const o = editing.o, fs = o.fs * cam.z;
  ta.style.left = ((o.x - cam.x) * cam.z - 4) + 'px'; ta.style.top = ((o.y - cam.y) * cam.z - 2) + 'px';
  ta.style.fontSize = fs + 'px'; ta.style.color = colOf(o.c);
  const top = (o.y - cam.y) * cam.z - 46;
  symbar.style.left = clamp((o.x - cam.x) * cam.z - 4, 8, Math.max(8, W - 360)) + 'px';
  symbar.style.top = (top < 60 ? (o.y - cam.y) * cam.z + Math.max(fs * 1.4, 20) * ta.value.split('\n').length + 12 : top - (symbar.offsetHeight > 44 ? symbar.offsetHeight - 40 : 0)) + 'px';
}
function sizeEditor(){
  if (!editing) return; const o = editing.o;
  measureCtx.font = `${o.fs * cam.z}px ${FONT}`;
  const L = ta.value.split('\n'); let w = 0; for (const l of L) w = Math.max(w, measureCtx.measureText(l + 'M').width);
  ta.style.width = Math.max(60, w + 12) + 'px'; ta.style.height = (L.length * o.fs * cam.z * 1.3 + 8) + 'px';
  positionEditor();
}
ta.addEventListener('input', sizeEditor);
ta.addEventListener('keydown', e => { if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); commitText(); } });
ta.addEventListener('blur', () => setTimeout(() => { if (editing && document.activeElement !== ta) commitText(); }, 0));
function commitText(){
  if (!editing) return; const { o, isNew } = editing; editing = null;
  const s = ta.value.replace(/\s+$/, ''); ta.hidden = true; symbar.hidden = true;
  if (!s) { if (!isNew) deleteObjects([o.id]); }
  else if (isNew) addObjects([Object.assign({}, o, { s })]);
  else if (s !== o.s) replaceObjects([[o, Object.assign({}, objs.get(o.id) || o, { s })]]);
  dirty();
}

/* ---------------- images ---------------- */
$('#imgBtn').addEventListener('click', () => $('#fileIn').click());
$('#fileIn').addEventListener('change', e => { const fs = [...e.target.files]; e.target.value = ''; placeImages(fs, null); });
document.addEventListener('paste', e => {
  if (typing()) return;
  const items = [...(e.clipboardData ? e.clipboardData.items : [])];
  const files = items.filter(i => i.kind === 'file' && i.type.startsWith('image/')).map(i => i.getAsFile()).filter(Boolean);
  if (files.length) { e.preventDefault(); placeImages(files, lastWorld); return; }
  const txt = e.clipboardData && e.clipboardData.getData('text/plain');
  if (txt && txt.trim()) {
    e.preventDefault(); const at = lastWorld || toWorld(W / 2, H / 2);
    addObjects([{ id: rid(), t:'text', x: r1(at.x), y: r1(at.y), s: txt.slice(0, 4000), c: prefs.ink, fs: r3(20 / cam.z), z: newZ(), by: me.name }]);
  }
});
cv.addEventListener('dragover', e => { e.preventDefault(); });
cv.addEventListener('drop', e => {
  e.preventDefault(); const { sx, sy } = evPos(e);
  const files = [...(e.dataTransfer ? e.dataTransfer.files : [])].filter(f => f.type.startsWith('image/'));
  if (files.length) placeImages(files, toWorld(sx, sy));
});
async function placeImages(files, at){
  let pos = at || toWorld(W * 0.3, H * 0.25), added = [];
  for (const f of files.slice(0, 8)) {
    try {
      const { src, w, h } = await compressImage(f);
      const maxW = (W * 0.55) / cam.z, k = Math.min(1, maxW / w, ((H * 0.6) / cam.z) / h);
      const o = { id: rid(), t:'image', x: r1(pos.x), y: r1(pos.y), w: r1(w * k), h: r1(h * k), sw:0, src, c:'ink', z: newZ(), by: me.name };
      added.push(o); pos = { x: pos.x + 30 / cam.z, y: pos.y + 30 / cam.z };
    } catch (err) { toast('That image could not be read. Try a PNG or JPG.'); }
  }
  if (added.length) { addObjects(added); setTool('select'); added.forEach(o => selection.add(o.id)); renderProps(); dirty(); }
}
function compressImage(file){
  return new Promise((resolve, reject) => {
    const url = URL.createObjectURL(file), im = new Image();
    im.onload = () => {
      URL.revokeObjectURL(url);
      let w = im.naturalWidth, h = im.naturalHeight; const nat = { w, h };
      let scale = Math.min(1, 1800 / Math.max(w, h));
      const c = document.createElement('canvas'), g = c.getContext('2d');
      const enc = (s, q) => { c.width = Math.max(1, Math.round(w * s)); c.height = Math.max(1, Math.round(h * s)); g.fillStyle = '#ffffff'; g.fillRect(0, 0, c.width, c.height); g.drawImage(im, 0, 0, c.width, c.height); let d = c.toDataURL('image/webp', q); if (!d.startsWith('data:image/webp')) d = c.toDataURL('image/jpeg', q); return d; };
      let q = 0.86, d = enc(scale, q);
      for (let i = 0; i < 10 && d.length > 230000; i++) { if (q > 0.6) q -= 0.1; else scale *= 0.8; d = enc(scale, q); }
      if (d.length > 240000) { reject(new Error('too big')); return; }
      resolve({ src: d, w: nat.w, h: nat.h });
    };
    im.onerror = () => { URL.revokeObjectURL(url); reject(new Error('bad image')); };
    im.src = url;
  });
}

/* ---------------- expression engine (calculator + graphs) ---------------- */
const NAMES = ['arcsin','arccos','arctan','asin','acos','atan','sinh','cosh','tanh','cosec','sin','cos','tan','sec','csc','cot','ln','log','sqrt','cbrt','abs','exp','floor','ceil','round','Ans','pi','e','x','C','P'].sort((a, b) => b.length - a.length);
function fact(n){ if (n < 0 || !Number.isInteger(n)) return NaN; if (n > 170) return Infinity; let r = 1; for (let i = 2; i <= n; i++) r *= i; return r; }
function nCr(n, r){ if (!Number.isInteger(n) || !Number.isInteger(r) || r < 0 || n < 0 || r > n) return r > n && Number.isInteger(n) && Number.isInteger(r) && r >= 0 ? 0 : NaN; r = Math.min(r, n - r); let v = 1; for (let i = 1; i <= r; i++) v = v * (n - r + i) / i; return Math.round(v); }
function nPr(n, r){ if (!Number.isInteger(n) || !Number.isInteger(r) || r < 0 || n < 0) return NaN; if (r > n) return 0; let v = 1; for (let i = 0; i < r; i++) v *= (n - i); return v; }
const toR = (a, E) => E.deg ? a * Math.PI / 180 : a, fromR = (a, E) => E.deg ? a * 180 / Math.PI : a;
const snapTrig = v => Math.abs(v) < 1e-14 ? 0 : v;
const F = {
  sin:(a, E) => snapTrig(Math.sin(toR(a[0], E))), cos:(a, E) => snapTrig(Math.cos(toR(a[0], E))),
  tan:(a, E) => { const r = toR(a[0], E); if (Math.abs(Math.cos(r)) < 1e-15) return NaN; return snapTrig(Math.tan(r)); },
  sec:(a, E) => 1 / Math.cos(toR(a[0], E)), csc:(a, E) => 1 / Math.sin(toR(a[0], E)), cot:(a, E) => 1 / Math.tan(toR(a[0], E)),
  asin:(a, E) => fromR(Math.asin(a[0]), E), acos:(a, E) => fromR(Math.acos(a[0]), E), atan:(a, E) => fromR(Math.atan(a[0]), E),
  sinh:a => Math.sinh(a[0]), cosh:a => Math.cosh(a[0]), tanh:a => Math.tanh(a[0]),
  ln:a => Math.log(a[0]), log:a => a.length > 1 ? Math.log(a[0]) / Math.log(a[1]) : Math.log10(a[0]),
  sqrt:a => Math.sqrt(a[0]), cbrt:a => Math.cbrt(a[0]), abs:a => Math.abs(a[0]), exp:a => Math.exp(a[0]),
  floor:a => Math.floor(a[0]), ceil:a => Math.ceil(a[0]), round:a => Math.round(a[0]),
};
F.arcsin = F.asin; F.arccos = F.acos; F.arctan = F.atan; F.cosec = F.csc;
function lex(src){
  let s = String(src).replace(/^\s*y\s*=\s*/i, '')
    .replace(/(sin|cos|tan)⁻¹/g, 'a$1').replace(/⁻¹/g, '^(-1)')
    .replace(/[×·]/g, '*').replace(/÷/g, '/').replace(/[−–]/g, '-').replace(/π/g, 'pi').replace(/√/g, 'sqrt').replace(/∛/g, 'cbrt')
    .replace(/²/g, '^2').replace(/³/g, '^3').replace(/\*\*/g, '^');
  const T = []; let i = 0;
  while (i < s.length) {
    const ch = s[i];
    if (/\s/.test(ch)) { i++; continue; }
    if (/[0-9.]/.test(ch)) { const m = /^(\d+\.?\d*|\.\d+)/.exec(s.slice(i)); if (!m) throw Error('Odd number near "' + s.slice(i, i + 4) + '"'); T.push({ k:'num', n: parseFloat(m[1]) }); i += m[1].length; continue; }
    if (/[A-Za-z]/.test(ch)) {
      const name = NAMES.find(n => s.startsWith(n, i)) || NAMES.find(n => n.length > 1 && s.slice(i, i + n.length).toLowerCase() === n.toLowerCase());
      if (!name) throw Error('Unknown "' + s.slice(i).match(/^[A-Za-z]+/)[0] + '"');
      T.push({ k:'id', v:name }); i += name.length; continue;
    }
    if ('+-*/^()!,'.includes(ch)) { T.push({ k:'op', v:ch }); i++; continue; }
    throw Error('Unexpected "' + ch + '"');
  }
  return T;
}
function compile(src, opt = {}){
  const T = lex(src); let i = 0;
  if (!T.length) throw Error('Nothing to work out');
  const peek = () => T[i], next = () => T[i++];
  const isOp = (t, v) => t && t.k === 'op' && t.v === v;
  const startsPrimary = t => t && (t.k === 'num' || (t.k === 'id' && t.v !== 'C' && t.v !== 'P') || isOp(t, '('));
  function expr(){
    let a = term();
    while (isOp(peek(), '+') || isOp(peek(), '-')) { const op = next().v, b = term(), l = a; a = op === '+' ? (x, E) => l(x, E) + b(x, E) : (x, E) => l(x, E) - b(x, E); }
    return a;
  }
  function term(){
    let a = unary();
    for (;;) {
      const t = peek(); if (!t) break;
      if (isOp(t, '*') || isOp(t, '/')) { next(); const b = unary(), l = a; a = t.v === '*' ? (x, E) => l(x, E) * b(x, E) : (x, E) => l(x, E) / b(x, E); }
      else if (t.k === 'id' && (t.v === 'C' || t.v === 'P')) { next(); const b = unary(), l = a, f = t.v === 'C' ? nCr : nPr; a = (x, E) => f(l(x, E), b(x, E)); }
      else if (startsPrimary(t)) { const b = power(), l = a; a = (x, E) => l(x, E) * b(x, E); }
      else break;
    }
    return a;
  }
  function unary(){ const t = peek(); if (isOp(t, '-') || isOp(t, '+')) { next(); const a = unary(); return t.v === '-' ? (x, E) => -a(x, E) : a; } return power(); }
  function power(){ const b = postfix(); if (isOp(peek(), '^')) { next(); const e = unary(); return (x, E) => Math.pow(b(x, E), e(x, E)); } return b; }
  function postfix(){ let a = primary(); while (isOp(peek(), '!')) { next(); const l = a; a = (x, E) => fact(l(x, E)); } return a; }
  function closeParen(){ if (isOp(peek(), ')')) next(); else if (peek()) throw Error('Missing )'); }
  function primary(){
    const t = next(); if (!t) throw Error('Expression ends too early');
    if (t.k === 'num') { const v = t.n; return () => v; }
    if (isOp(t, '(')) { const a = expr(); closeParen(); return a; }
    if (t.k === 'id') {
      if (t.v === 'pi') return () => Math.PI;
      if (t.v === 'e') return () => Math.E;
      if (t.v === 'x') { if (!opt.allowX) throw Error('x only works in graphs'); return x => x; }
      if (t.v === 'Ans') return (x, E) => E.ans;
      const fn = F[t.v];
      if (fn) {
        let args;
        if (isOp(peek(), '(')) { next(); args = [expr()]; while (isOp(peek(), ',')) { next(); args.push(expr()); } closeParen(); }
        else args = [power()];
        if (args.length === 1) { const a0 = args[0]; return (x, E) => fn([a0(x, E)], E); }
        return (x, E) => fn(args.map(g => g(x, E)), E);
      }
    }
    throw Error('Unexpected "' + (t.v ?? t.n) + '"');
  }
  const f = expr(); if (i < T.length) throw Error('Unexpected "' + (T[i].v ?? T[i].n) + '"');
  return f;
}
function fmtNum(v){
  if (!isFinite(v)) return v > 0 ? '∞' : v < 0 ? '−∞' : 'Math error';
  if (Math.abs(v) < 1e-13) v = 0;
  const a = Math.abs(v);
  if (a !== 0 && (a >= 1e10 || a < 1e-6)) { const [m, ex] = v.toExponential(8).split('e'); return parseFloat(m) + '×10^' + parseInt(ex, 10); }
  return String(parseFloat(v.toPrecision(11))).replace('-', '−');
}
function toFrac(v){
  if (!isFinite(v) || Number.isInteger(v)) return null;
  const sign = v < 0 ? '−' : ''; const x = Math.abs(v);
  let h1 = 1, h0 = 0, k1 = 0, k0 = 1, b = x;
  for (let i = 0; i < 40; i++) {
    const a = Math.floor(b); [h1, h0] = [a * h1 + h0, h1]; [k1, k0] = [a * k1 + k0, k1];
    if (Math.abs(x - h1 / k1) < 1e-10 * Math.max(1, x)) break;
    if (b - a < 1e-12) break; b = 1 / (b - a);
  }
  if (k1 > 100000 || Math.abs(x - h1 / k1) > 1e-9 * Math.max(1, x)) return null;
  return sign + h1 + '/' + k1;
}

/* ---------------- calculator ---------------- */
const calc = { deg: store.get('fmwb:deg') !== '0', frac:false, ans:0, last:null, hist:[], hi:-1 };
const cIn = $('#calcIn'), cOut = $('#calcOut');
if (matchMedia('(pointer: coarse)').matches) cIn.setAttribute('inputmode', 'none');
function toggleCalc(force, quiet){
  const p = $('#calc'); const show = force ?? p.hidden; p.hidden = !show;
  $('#calcBtn').setAttribute('aria-pressed', String(show));
  if (show && !quiet && !matchMedia('(pointer: coarse)').matches) setTimeout(() => cIn.focus(), 0);
  saveViewSoon();
}
$('#calcBtn').addEventListener('click', () => toggleCalc());
$('#calcX').addEventListener('click', () => toggleCalc(false));
function renderCalcModes(){
  $('#cDeg').textContent = calc.deg ? 'DEG' : 'RAD'; $('#indAng').textContent = calc.deg ? 'DEG' : 'RAD';
  $('#cFrac').setAttribute('aria-pressed', String(calc.frac)); $('#indFrac').className = calc.frac ? '' : 'off';
  $('#indAns').className = calc.last ? '' : 'off';
}
function showResult(){
  cOut.classList.remove('err');
  if (!calc.last) { cOut.textContent = '0'; return; }
  const v = calc.last.v; const fr = calc.frac ? toFrac(v) : null;
  cOut.textContent = fr || fmtNum(v);
}
function evaluate(){
  const src = cIn.value.trim(); if (!src) return;
  try {
    const v = compile(src, { allowX:false })(0, { deg: calc.deg, ans: calc.ans });
    if (Number.isNaN(v)) { cOut.textContent = 'Math error: no real answer'; cOut.classList.add('err'); return; }
    calc.ans = v; calc.last = { src, v };
    calc.hist.unshift({ src, v }); calc.hist = calc.hist.slice(0, 12); calc.hi = -1;
    showResult(); renderHist(); renderCalcModes();
  } catch (err) { cOut.textContent = 'Syntax error: ' + err.message; cOut.classList.add('err'); }
}
function renderHist(){
  const h = $('#calcHist'); h.textContent = '';
  for (const it of calc.hist.slice(0, 6)) h.appendChild(elt('button', { type:'button', title:'Use this calculation again', onclick:() => { cIn.value = it.src; cIn.focus(); } }, [elt('span', { text: it.src }), elt('span', { text: '= ' + fmtNum(it.v) })]));
}
$$('#calc .k').forEach(b => {
  b.addEventListener('pointerdown', e => e.preventDefault());
  b.addEventListener('click', () => {
    if (b.dataset.i != null) {
      let s = b.dataset.i;
      if (!cIn.value && calc.last && /^[+\−×÷^²!CP]/.test(s)) s = 'Ans' + s;
      insertAtCursor(cIn, s);
    } else if (b.dataset.a === 'eq') evaluate();
    else if (b.dataset.a === 'ac') { cIn.value = ''; calc.last = null; showResult(); renderCalcModes(); cIn.focus(); }
    else if (b.dataset.a === 'del') {
      const a = cIn.selectionStart ?? cIn.value.length, z = cIn.selectionEnd ?? a;
      if (a !== z) cIn.value = cIn.value.slice(0, a) + cIn.value.slice(z);
      else if (a > 0) { const m = /(sin⁻¹\(|cos⁻¹\(|tan⁻¹\(|sin\(|cos\(|tan\(|log\(|abs\(|ln\(|Ans|×10\^|√\(|∛\(|e\^\(|10\^\()$/.exec(cIn.value.slice(0, a)); const n = m ? m[0].length : 1; cIn.value = cIn.value.slice(0, a - n) + cIn.value.slice(a); cIn.setSelectionRange(a - n, a - n); }
      cIn.focus();
    }
  });
});
cIn.addEventListener('keydown', e => {
  if (e.key === 'Enter') { e.preventDefault(); evaluate(); }
  else if (e.key === 'ArrowUp' && calc.hist.length) { e.preventDefault(); calc.hi = Math.min(calc.hi + 1, calc.hist.length - 1); cIn.value = calc.hist[calc.hi].src; }
  else if (e.key === 'ArrowDown' && calc.hi > 0) { e.preventDefault(); calc.hi--; cIn.value = calc.hist[calc.hi].src; }
  else if (e.key === 'Escape') { cIn.blur(); }
});
$('#cDeg').addEventListener('click', () => { calc.deg = !calc.deg; store.set('fmwb:deg', calc.deg ? '1' : '0'); renderCalcModes(); });
$('#cFrac').addEventListener('click', () => { calc.frac = !calc.frac; renderCalcModes(); showResult(); });
$('#cCopy').addEventListener('click', () => {
  if (!calc.last) return; const t = cOut.textContent;
  try { navigator.clipboard.writeText(t).then(() => toast('Copied ' + t), () => toast('Copy is blocked here. Select the answer instead.')); } catch(e) { toast('Copy is blocked here.'); }
});
$('#cBoard').addEventListener('click', () => {
  if (!calc.last) { toast('Work something out first'); return; }
  const at = toWorld(W * 0.42, H * 0.45);
  const s = calc.last.src + ' = ' + cOut.textContent;
  addObjects([{ id: rid(), t:'text', x: r1(at.x), y: r1(at.y), s, c: prefs.ink, fs: r3(22 / cam.z), z: newZ(), by: me.name }]);
  toast('Written on the board');
});
renderCalcModes();

/* ---------------- graph editor ---------------- */
let gEditId = null, gTimer = 0, gBefore = null;
function openGraphEditor(id){
  const o = objs.get(id); if (!o) return;
  gEditId = id; gBefore = o;
  const box = $('#gfs'); box.textContent = '';
  for (let i = 0; i < 4; i++) {
    const inp = elt('input', { class:'fin', id:'gf' + i, autocomplete:'off', spellcheck:'false', placeholder: i ? 'add another function' : 'x^2 - 4', 'aria-label': 'Function ' + (i + 1) });
    inp.value = o.fx[i] || '';
    inp.addEventListener('input', queueGraph);
    const dot = elt('span', { class:'cdot' }); dot.style.background = colOf(GCOLS[i]);
    box.appendChild(elt('div', { class:'frow' }, [dot, elt('label', { for:'gf' + i, text:'y =' }), inp]));
  }
  $('#gx0').value = o.xa; $('#gx1').value = o.xb; $('#gy0').value = o.ya; $('#gy1').value = o.yb;
  ['gx0','gx1','gy0','gy1'].forEach(k => { $('#' + k).oninput = queueGraph; });
  $('#gerr').textContent = '';
  $('#gpanel').hidden = false;
  setTimeout(() => { const f = $('#gf0'); f.focus(); f.select(); }, 0);
}
function queueGraph(){ clearTimeout(gTimer); gTimer = setTimeout(applyGraph, 350); }
function applyGraph(final){
  const o = objs.get(gEditId); if (!o) { $('#gpanel').hidden = true; return; }
  const fx = [0, 1, 2, 3].map(i => $('#gf' + i).value.trim().slice(0, 120));
  let err = '';
  fx.forEach((s, i) => { const el = $('#gf' + i); el.classList.remove('bad'); if (!s) return; try { compile(s, { allowX:true }); } catch(e) { el.classList.add('bad'); err = err || ('Line ' + (i + 1) + ': ' + e.message); } });
  const nv = k => { const s = $('#' + k).value.trim().replace('−', '-'); try { return compile(s)(0, { deg:false, ans:0 }); } catch(e) { return NaN; } };
  let xa = nv('gx0'), xb = nv('gx1'), ya = nv('gy0'), yb = nv('gy1');
  if (![xa, xb, ya, yb].every(num) || xb <= xa || yb <= ya) { err = err || 'Window needs min < max for both x and y.'; xa = o.xa; xb = o.xb; ya = o.ya; yb = o.yb; }
  $('#gerr').textContent = err;
  const n = Object.assign({}, o, { fx, xa, xb, ya, yb });
  if (JSON.stringify(n) !== JSON.stringify(o)) { objs.set(n.id, n); dirty(); if (!final) writeObj(n, false); }
  if (final) { if (gBefore && JSON.stringify(gBefore) !== JSON.stringify(n)) replaceObjects([[gBefore, n]]); gBefore = n; }
}
function closeGraph(){ if (gEditId) { clearTimeout(gTimer); applyGraph(true); } gEditId = null; $('#gpanel').hidden = true; }
$('#gX').addEventListener('click', closeGraph);
$('#gpanel').addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); clearTimeout(gTimer); applyGraph(true); } if (e.key === 'Escape') closeGraph(); });

/* ---------------- draggable panels ---------------- */
$$('[data-drag]').forEach(h => {
  h.addEventListener('pointerdown', e => {
    if (e.target.closest('button')) return;
    const p = $('#' + h.dataset.drag), r = p.getBoundingClientRect(), ar = app.getBoundingClientRect();
    const ox = e.clientX - r.left, oy = e.clientY - r.top; h.setPointerCapture(e.pointerId);
    p.style.transform = 'none'; p.style.right = 'auto'; p.style.left = (r.left - ar.left) + 'px'; p.style.top = (r.top - ar.top) + 'px';
    const mv = ev => { p.style.left = clamp(ev.clientX - ar.left - ox, -r.width + 60, ar.width - 60) + 'px'; p.style.top = clamp(ev.clientY - ar.top - oy, 0, ar.height - 40) + 'px'; };
    const up = () => { h.removeEventListener('pointermove', mv); h.removeEventListener('pointerup', up); h.removeEventListener('pointercancel', up); };
    h.addEventListener('pointermove', mv); h.addEventListener('pointerup', up); h.addEventListener('pointercancel', up);
  });
});

/* ---------------- people ---------------- */
function initials(n){ const p = n.trim().split(/\s+/); return ((p[0] || '?')[0] + (p[1] ? p[1][0] : (p[0] || '')[1] || '')).toUpperCase(); }
function renderPeople(){
  const box = $('#people'); box.textContent = '';
  const list = peers.filter(p => p.primary);
  const meBtn = elt('button', { class:'av me', type:'button', title: (me.name || 'You') + ' (you) · change name', 'aria-label':'You: ' + (me.name || 'no name yet'), text: initials(me.name || '?'), onclick:() => openJoin() });
  meBtn.style.background = myColor(); box.appendChild(meBtn);
  for (const p of list.slice(0, 7)) {
    const name = safeName(p.presence && p.presence.name);
    const b = elt('button', { class:'av' + (followPeer === p.peer ? ' following' : ''), type:'button', title: name + (p.isMe ? ' (your other tab)' : '') + (p.guest ? ' · guest' : ''), 'aria-label': name, text: initials(name), onclick: ev => personMenu(p, ev.currentTarget) });
    b.style.background = safeCol(p.presence && p.presence.col); box.appendChild(b);
  }
  if (list.length > 7) box.appendChild(elt('span', { class:'boardchip', text:'+' + (list.length - 7) }));
}
function personMenu(p, anchor){
  const m = $('#pmenu'); m.textContent = '';
  const name = safeName(p.presence && p.presence.name);
  m.appendChild(elt('div', { class:'mlabel', text: name }));
  m.appendChild(elt('button', { type:'button', text:'Jump to where they are', onclick:() => { closeMenus(); const v = p.presence && p.presence.v; const c = p.presence && p.presence.cur; if (Array.isArray(v) && v.every(num)) centerOn(v[0], v[1], v[2]); else if (Array.isArray(c) && c.every(num)) centerOn(c[0], c[1]); else toast(name + ' hasn’t moved yet'); } }));
  const f = followPeer === p.peer;
  m.appendChild(elt('button', { type:'button', 'aria-pressed': String(f), text: f ? 'Following their screen' : 'Follow their screen', onclick:() => { closeMenus(); if (f) stopFollow(); else { followPeer = p.peer; presenceSet({ follow:{ of:p.peer } }); toast('Following ' + name + '. Pan or zoom to stop.'); renderPeople(); dirty(); } } }));
  openMenuAt(m, anchor);
}
function openMenuAt(m, anchor){
  m.hidden = false; const r = anchor.getBoundingClientRect(), ar = app.getBoundingClientRect();
  m.style.top = (r.bottom - ar.top + 8) + 'px'; m.style.left = clamp(r.right - ar.left - m.offsetWidth, 8, ar.width - m.offsetWidth - 8) + 'px';
}
function closeMenus(){ $('#menu').hidden = true; $('#pmenu').hidden = true; }
document.addEventListener('pointerdown', e => { if (!e.target.closest('.menu') && !e.target.closest('#menuBtn') && !e.target.closest('.av')) closeMenus(); });

/* ---------------- name / invite / menu ---------------- */
function openJoin(msg){
  const sc = $('#joinScrim'); sc.hidden = false; $('#nameIn').value = me.name;
  $('#joinErr').textContent = msg || ''; $('#joinErr').hidden = !msg;
  setTimeout(() => { $('#nameIn').focus(); $('#nameIn').select(); }, 0);
}
$('#joinForm').addEventListener('submit', e => {
  e.preventDefault(); const n = Array.from($('#nameIn').value).filter(ch => { const c = ch.codePointAt(0); return !(c < 32 || (c >= 127 && c < 160) || (c >= 0x200b && c <= 0x200f) || (c >= 0x2028 && c <= 0x202e) || (c >= 0x2066 && c <= 0x2069)); }).join('').trim().slice(0, 24);
  if (n.length < 2) { $('#joinErr').textContent = 'Use at least 2 characters.'; $('#joinErr').hidden = false; $('#nameIn').focus(); return; }
  const taken = S.open ? nameTakenBy(n) : null;
  if (taken) { $('#joinErr').textContent = 'Someone on this board is already called ' + taken.name + '. Try another name.'; $('#joinErr').hidden = false; $('#nameIn').focus(); return; }
  me.name = n; store.set('fmwb:name', n);
  $('#joinScrim').hidden = true; $('#homeName').textContent = n;
  $('#nameIn').blur(); setTimeout(unNudge, 50); setTimeout(unNudge, 400);
  if (S.open) upsertMe();
  presenceSet({ name:n }); renderPeople();
});
function boardLink(){ return location.href.split('#')[0] + '#' + board; }
$('#invBtn').addEventListener('click', () => { $('#invScrim').hidden = false; $('#linkIn').value = boardLink(); });
$('#invClose').addEventListener('click', () => { $('#invScrim').hidden = true; });
$('#copyLink').addEventListener('click', () => {
  const l = boardLink(), inp = $('#linkIn');
  try { navigator.clipboard.writeText(l).then(() => toast('Link copied'), () => { inp.select(); toast('Press Ctrl C to copy'); }); } catch(e) { inp.select(); toast('Press Ctrl C to copy'); }
});
$('#newBoard').addEventListener('click', () => { $('#invScrim').hidden = true; location.hash = 'home'; });
$$('.scrim').forEach(s => s.addEventListener('pointerdown', e => { if (e.target === s && s.id !== 'joinScrim' && s.id !== 'home') s.hidden = true; }));

$('#menuBtn').addEventListener('click', e => {
  const m = $('#menu'); if (!m.hidden) { closeMenus(); return; } m.textContent = '';
  m.appendChild(elt('div', { class:'mlabel', text:'Paper' }));
  for (const [k, l] of [['squares','Squared'], ['dots','Dotted'], ['plain','Plain']])
    m.appendChild(elt('button', { type:'button', 'aria-pressed': String(prefs.bg === k), text:l, onclick:() => { prefs.bg = k; store.set('fmwb:bg', k); closeMenus(); dirty(); } }));
  m.appendChild(elt('div', { class:'hsep' }));
  m.appendChild(elt('button', { type:'button', 'aria-pressed': String(prefs.fingerPans), text:'Finger pans, stylus draws', title:'For tablets with a pen', onclick:() => { prefs.fingerPans = !prefs.fingerPans; store.set('fmwb:fp', prefs.fingerPans ? '1' : '0'); closeMenus(); toast(prefs.fingerPans ? 'One finger now pans. Your stylus still draws.' : 'Fingers draw again'); } }));
  m.appendChild(elt('button', { type:'button', text:'Save board as image', onclick:() => { closeMenus(); exportPng(); } }));
  m.appendChild(elt('button', { type:'button', text:'Keyboard shortcuts', onclick:() => { closeMenus(); $('#keysScrim').hidden = false; } }));
  m.appendChild(elt('button', { type:'button', text:'Change my name', onclick:() => { closeMenus(); openJoin(); } }));
  m.appendChild(elt('button', { type:'button', text:'My boards', onclick:() => { closeMenus(); location.hash = 'home'; } }));
  m.appendChild(elt('div', { class:'hsep' }));
  m.appendChild(elt('button', { type:'button', class:'danger', text:'Clear board…', onclick:() => { closeMenus(); if (!objs.size) { toast('The board is already empty'); return; } $('#confirmScrim').hidden = false; } }));
  openMenuAt(m, e.currentTarget);
});
$('#kClose').addEventListener('click', () => { $('#keysScrim').hidden = true; });
$('#cfNo').addEventListener('click', () => { $('#confirmScrim').hidden = true; });
$('#cfYes').addEventListener('click', () => { $('#confirmScrim').hidden = true; deleteObjects([...objs.keys()]); toast('Board cleared. Ctrl Z brings it back.'); });

$('#undoBtn').addEventListener('click', undo); $('#redoBtn').addEventListener('click', redo);
$('#zIn').addEventListener('click', () => { stopFollow(true); zoomAt(W / 2, H / 2, cam.z * 1.25); });
$('#zOut').addEventListener('click', () => { stopFollow(true); zoomAt(W / 2, H / 2, cam.z / 1.25); });
$('#zoomPct').addEventListener('click', () => { stopFollow(true); zoomAt(W / 2, H / 2, 1); });
$('#zFit').addEventListener('click', () => { stopFollow(true); fitAll(); });

async function exportPng(){
  if (!objs.size) { toast('Nothing to save yet'); return; }
  let b = [Infinity, Infinity, -Infinity, -Infinity];
  for (const o of objs.values()) { const q = bbox(o); b = [Math.min(b[0], q[0]), Math.min(b[1], q[1]), Math.max(b[2], q[2]), Math.max(b[3], q[3])]; }
  const pad = 40, w = b[2] - b[0] + pad * 2, h = b[3] - b[1] + pad * 2, s = Math.min(2, 8000 / Math.max(w, h));
  const c = document.createElement('canvas'); c.width = Math.ceil(w * s); c.height = Math.ceil(h * s);
  const g = c.getContext('2d'); g.fillStyle = T.paper; g.fillRect(0, 0, c.width, c.height);
  g.setTransform(s, 0, 0, s, (-b[0] + pad) * s, (-b[1] + pad) * s);
  for (const o of sortedObjs()) drawObj(g, o, s, false);
  c.toBlob(blob => {
    if (!blob) { toast('Could not make the image'); return; }
    const a = document.createElement('a'); a.href = URL.createObjectURL(blob);
    a.download = (meta.name || 'whiteboard').replace(/[^\w\- ]+/g, '').trim() + '.png';
    document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(a.href), 4000);
  }, 'image/png');
}

let toastT = 0;
function toast(msg, ms = 2600){ const t = $('#toast'); t.textContent = msg; t.hidden = false; clearTimeout(toastT); toastT = setTimeout(() => { t.hidden = true; }, ms); }

/* ---------------- boot ---------------- */
readTheme();
if (matchMedia('(pointer: coarse)').matches) {
  const ul = $('#empty ul'); ul.textContent = '';
  for (const [k, t] of [['Pencil', 'Writes. Fingers pan and pinch to zoom, and a resting palm is ignored'], ['No stylus?', 'One finger writes, two fingers move and zoom'], ['Photo icon', 'Add a picture of the question'], ['Calculator', 'Bottom of the toolbar, next to graphs']])
    ul.appendChild(elt('li', {}, [elt('kbd', { text:k }), elt('span', { text:t })]));
}
updateHist();
resize();
renderProps();
if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { bboxCache = new WeakMap(); orderDirty = true; dirty(); });
route();
})();
