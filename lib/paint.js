// Painting: a bitmap and the strokes that change it. Pure, so the picture on screen is exactly
// what proofs/spec.pl says it is. Colours are numbers 0xRRGGBB.
//
// A bitmap: { w, h, px: Uint32Array (or an array) of colours, row by row }

export function bitmap(w, h, bg = 0xffffff) {
  if (!Number.isInteger(w) || !Number.isInteger(h) || w < 1 || h < 1 || w * h > 4_000_000) throw new Error('canvas: a size from 1 by 1 to 2000 by 2000');
  return { w, h, px: new Uint32Array(w * h).fill(bg) };
}
export const copyOf = (b) => ({ w: b.w, h: b.h, px: b.px.slice() });
export const get = (b, x, y) => b.px[y * b.w + x];

// the dirty box of a change, so only that part is redrawn: [x0, y0, x1, y1] inclusive, or null
const box = () => ({ x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity });
const mark = (d, x, y) => { if (x < d.x0) d.x0 = x; if (y < d.y0) d.y0 = y; if (x > d.x1) d.x1 = x; if (y > d.y1) d.y1 = y; };
const done = (d) => (d.x1 < d.x0 ? null : [d.x0, d.y0, d.x1, d.y1]);

function plot(b, x, y, c, d) {
  if (x < 0 || y < 0 || x >= b.w || y >= b.h) return;
  const i = y * b.w + x;
  if (b.px[i] !== c) { b.px[i] = c; mark(d, x, y); }
}

// a round dot of radius r (r 0 is one pixel): the pixels whose centres are within r
function disc(b, cx, cy, r, c, d) {
  const R = Math.max(0, r);
  const ir = Math.ceil(R);
  for (let y = -ir; y <= ir; y++) for (let x = -ir; x <= ir; x++) if (x * x + y * y <= R * R + 0.25) plot(b, cx + x, cy + y, c, d);
}
function square(b, cx, cy, r, c, d) {
  const ir = Math.round(Math.max(0, r));
  for (let y = -ir; y <= ir; y++) for (let x = -ir; x <= ir; x++) plot(b, cx + x, cy + y, c, d);
}

// the points of a line from one pixel to another, both ends included (Bresenham)
export function linePoints(x0, y0, x1, y1) {
  const pts = [];
  const dx = Math.abs(x1 - x0), dy = -Math.abs(y1 - y0), sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
  let err = dx + dy, x = x0, y = y0;
  for (;;) {
    pts.push([x, y]);
    if (x === x1 && y === y1) return pts;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x += sx; }
    if (e2 <= dx) { err += dx; y += sy; }
  }
}

// a small fixed sequence for the spray can, so a spray is the same every time it is replayed
export function sprayPoints(cx, cy, r, seed, n = 24) {
  let s = (seed >>> 0) || 1;
  const rnd = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
  const pts = [];
  for (let k = 0; k < n; k++) {
    const a = rnd() * 2 * Math.PI, d = Math.sqrt(rnd()) * r;
    pts.push([Math.round(cx + d * Math.cos(a)), Math.round(cy + d * Math.sin(a))]);
  }
  return pts;
}

// flood fill from a pixel: every pixel joined to it (up, down, left, right) with its colour
export function fillRegion(b, x, y, c, d) {
  if (x < 0 || y < 0 || x >= b.w || y >= b.h) return;
  const { w, h, px } = b;
  const from = px[y * w + x];
  if (from === c) return;
  const stack = [x, y];
  // scanlines: fill a run, then seed the rows above and below once per run that matches
  const seed = (l, r, row) => {
    let inRun = false;
    for (let i = l; i <= r; i++) {
      const m = px[row * w + i] === from;
      if (m && !inRun) stack.push(i, row);
      inRun = m;
    }
  };
  while (stack.length) {
    const py = stack.pop(), sx = stack.pop();
    if (px[py * w + sx] !== from) continue;
    let l = sx, r = sx;
    while (l > 0 && px[py * w + l - 1] === from) l--;
    while (r < w - 1 && px[py * w + r + 1] === from) r++;
    for (let i = l; i <= r; i++) px[py * w + i] = c;
    mark(d, l, py); mark(d, r, py);
    if (py > 0) seed(l, r, py - 1);
    if (py < h - 1) seed(l, r, py + 1);
  }
}

// a stroke changes the bitmap in place and returns the dirty box.
// stroke: { op: 'dot'|'line'|'fill'|'spray'|'clear', ... } with brush { colour, size, tip: 'round'|'square' }
export function apply(b, stroke, brush) {
  const d = box();
  const c = brush.colour, r = brush.size / 2, tip = brush.tip === 'square' ? square : disc;
  switch (stroke.op) {
    case 'dot': tip(b, Math.round(stroke.x), Math.round(stroke.y), r, c, d); break;
    case 'line': for (const [x, y] of linePoints(Math.round(stroke.x1), Math.round(stroke.y1), Math.round(stroke.x2), Math.round(stroke.y2))) tip(b, x, y, r, c, d); break;
    case 'spray': for (const [x, y] of sprayPoints(Math.round(stroke.x), Math.round(stroke.y), Math.max(2, brush.size * 2), stroke.seed ?? 1)) plot(b, x, y, c, d); break;
    case 'fill': fillRegion(b, Math.round(stroke.x), Math.round(stroke.y), c, d); break;
    case 'clear': for (let i = 0; i < b.px.length; i++) if (b.px[i] !== c) { b.px[i] = c; mark(d, i % b.w, Math.floor(i / b.w)); } break;
    default: throw new Error(`paint: ${stroke.op} isn't a stroke`);
  }
  return done(d);
}

// ---- colours

export const NAMED = {
  black: 0x000000, white: 0xffffff, red: 0xe53935, orange: 0xfb8c00, yellow: 0xfdd835, green: 0x43a047, lime: 0xc0ca33,
  teal: 0x00897b, cyan: 0x00acc1, blue: 0x1e88e5, navy: 0x283593, purple: 0x8e24aa, pink: 0xd81b60, brown: 0x6d4c41,
  grey: 0x9e9e9e, gray: 0x9e9e9e, silver: 0xcfd8dc, gold: 0xffb300, sky: 0x81d4fa, cream: 0xfff8e1
};
export function colour(v) {
  if (typeof v === 'number' && Number.isInteger(v) && v >= 0 && v <= 0xffffff) return v;
  const s = String(v).trim().toLowerCase();
  if (s in NAMED) return NAMED[s];
  let m = /^#([0-9a-f]{6})$/.exec(s);
  if (m) return parseInt(m[1], 16);
  m = /^#([0-9a-f])([0-9a-f])([0-9a-f])$/.exec(s);
  if (m) return parseInt(m[1] + m[1] + m[2] + m[2] + m[3] + m[3], 16);
  throw new Error(`${v} isn't a colour I know (try red, #ff8800)`);
}
export const hex = (c) => `#${c.toString(16).padStart(6, '0')}`;
