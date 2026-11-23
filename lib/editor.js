// The editor: select, move and resize shapes with the pointer, and select with a rubber band.
// Pure: edit(state, scene, event) -> { state, scene }. A Prolog program hands its pointer events
// to it with edit(down(X, Y)), edit(drag(X, Y)) and edit(up(X, Y)).
//
// state: { mode: 'idle' | 'moving' | 'resizing' | 'band', from: [x, y], last: [x, y], handle?, box? }

import { bounds, hit, move, scaleTo, select } from './scene.js';

export const HANDLE = 6; // half the size of a resize handle
export const idle = () => ({ mode: 'idle' });

// the four corner handles of the selection's single item: [[name, x, y]]
export function handles(s) {
  if (s.selected.length !== 1) return [];
  const [x, y, w, h] = bounds(s, s.selected[0]);
  return [['nw', x, y], ['ne', x + w, y], ['sw', x, y + h], ['se', x + w, y + h]];
}
const onHandle = (s, x, y) => handles(s).find(([, hx, hy]) => Math.abs(x - hx) <= HANDLE + 2 && Math.abs(y - hy) <= HANDLE + 2)?.[0] ?? null;

// the box from the corner opposite the handle to the pointer
function resized([x, y, w, h], handle, px, py) {
  const ax = handle.includes('w') ? x + w : x, ay = handle.includes('n') ? y + h : y;
  const x0 = Math.min(ax, px), y0 = Math.min(ay, py);
  return [x0, y0, Math.max(1, Math.abs(px - ax)), Math.max(1, Math.abs(py - ay))];
}

export function edit(st, s, ev) {
  const [x, y] = ev.at;
  switch (ev.type) {
    case 'down': {
      const h = onHandle(s, x, y);
      if (h) return { state: { mode: 'resizing', handle: h, from: [x, y], last: [x, y], start: bounds(s, s.selected[0]) }, scene: s };
      const id = hit(s, x, y);
      if (id) {
        const sel = ev.add ? (s.selected.includes(id) ? s.selected.filter((v) => v !== id) : [...s.selected, id]) : s.selected.includes(id) ? s.selected : [id];
        return { state: { mode: 'moving', from: [x, y], last: [x, y] }, scene: select(s, sel) };
      }
      return { state: { mode: 'band', from: [x, y], last: [x, y], box: [x, y, 0, 0] }, scene: ev.add ? s : select(s, []) };
    }
    case 'drag': {
      if (st.mode === 'moving') {
        const dx = x - st.last[0], dy = y - st.last[1];
        let s2 = s;
        for (const id of s.selected) s2 = move(s2, id, dx, dy);
        return { state: { ...st, last: [x, y] }, scene: s2 };
      }
      if (st.mode === 'resizing') return { state: { ...st, last: [x, y] }, scene: scaleTo(s, s.selected[0], resized(st.start, st.handle, x, y)) };
      if (st.mode === 'band') {
        const [fx, fy] = st.from;
        return { state: { ...st, last: [x, y], box: [Math.min(fx, x), Math.min(fy, y), Math.abs(x - fx), Math.abs(y - fy)] }, scene: s };
      }
      return { state: st, scene: s };
    }
    case 'up': {
      if (st.mode === 'band') {
        const [bx, by, bw, bh] = st.box;
        const inside = [];
        for (const l of s.layers) {
          if (!l.shown || l.locked) continue;
          for (const id of l.items) { const [ix, iy, iw, ih] = bounds(s, id); if (ix >= bx && iy >= by && ix + iw <= bx + bw && iy + ih <= by + bh) inside.push(id); }
        }
        return { state: idle(), scene: select(s, ev.add ? [...new Set([...s.selected, ...inside])] : inside) };
      }
      return { state: idle(), scene: s };
    }
    default: return { state: st, scene: s };
  }
}
