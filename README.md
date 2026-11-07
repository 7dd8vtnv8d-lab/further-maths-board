# Further Maths Board

A shared, endless whiteboard for working through maths together.

**Open the link → type your name → start writing.** No accounts, no sign-up, no server.

## Using it

- Make a board from the home page, press **Invite**, and send the link to your group.
- Everyone gets their own tools and their own view. Nobody takes over anyone else's screen.
- Each person is given a random colour that nobody else on that board has.
- Your name is remembered in your browser, so every tab and every board uses the same one. Reopening a link puts you back where you were.

**Works with:**
- **Apple Pencil / stylus:** the pen writes, fingers pan and pinch to zoom, and a resting palm is ignored.
- **Fingers:** one finger writes, two fingers move and zoom.
- **Mouse / trackpad:** scroll or pinch to zoom, and Space-drag or right-drag to pan.

**Tools:** pen, highlighter, eraser, laser pointer, straight lines (Shift snaps to 15°), arrows, rectangles, circles, x–y axes, text with maths symbols, y = f(x) graphs, a scientific calculator, pasted or uploaded images, follow someone's screen, undo/redo, and save as PNG.

## How it works

- The site is plain static files hosted on GitHub Pages. There is no server and no database.
- Browsers connect directly to each other (WebRTC) when the network allows it. Public Nostr relays are used only to introduce browsers to each other, and that introduction is encrypted with a key that comes from the board link.
- Every message is also sent through free public MQTT brokers (`relay.js`), so boards still sync on mobile data and strict Wi-Fi, where direct connections often fail. Those messages are end-to-end encrypted (AES-256-GCM, with a key derived from the board link), and the topic name is a hash, so the brokers can neither read the boards nor find them.
- Each board is saved in the browser of everyone who uses it (IndexedDB) and syncs when two or more people have it open.
- Anyone with a board's link can join and edit that board, so only share links with people you trust.

## Third-party code

- [Trystero](https://github.com/dmotz/trystero) 0.25.4 (MIT), bundled locally in `trystero.js`.
- Fonts (SIL Open Font License 1.1), self-hosted in `fonts/`: Atkinson Hyperlegible, Bricolage Grotesque, JetBrains Mono.
