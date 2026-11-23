// Pointers: a Prolog description of a pointer becomes a CSS cursor. Pure.
//
//   arrow, crosshair, move, grab, grabbing, text, hand, none, cell, forbidden   the system's own
//   circle(R, Colour)        a ring of radius R (a brush's size), its centre the hot spot
//   cross(Size, Colour)      a thin cross
//   glyph(Text)              a character or emoji, e.g. glyph("🪣"), hot spot in the middle
//   glyph(Text, HotX, HotY)
//   svg(Text, HotX, HotY)    your own SVG
// -> { css, w, h, hot: [x, y] }  (browsers show pointers up to 128 by 128)

const SYSTEM = { arrow: 'default', crosshair: 'crosshair', move: 'move', grab: 'grab', grabbing: 'grabbing', text: 'text', hand: 'pointer', none: 'none', cell: 'cell', forbidden: 'not-allowed' };
export const MAX = 128;
const esc = (s) => s.replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);
const COLOUR = /^(#[0-9a-fA-F]{3}|#[0-9a-fA-F]{6}|[a-z]{3,12})$/;
const url = (svg, hx, hy, fallback) => `url("data:image/svg+xml,${encodeURIComponent(svg)}") ${hx} ${hy}, ${fallback}`;

export function cursor(spec) {
  if (typeof spec === 'string') {
    if (!(spec in SYSTEM)) throw new Error(`${spec} isn't a pointer (try ${Object.keys(SYSTEM).join(', ')})`);
    return { css: SYSTEM[spec], w: 0, h: 0, hot: [0, 0] };
  }
  const { f, a } = spec ?? {};
  const n = (v, lo, hi, what) => { if (typeof v !== 'number' || !Number.isFinite(v) || v < lo || v > hi) throw new Error(`${what}: ${lo} to ${hi}`); return Math.round(v); };
  const c = (v) => { if (typeof v !== 'string' || !COLOUR.test(v)) throw new Error(`${v}: a colour such as red or #ff8800`); return v; };
  if (f === 'circle' && a.length === 2) {
    const r = n(a[0], 1, 60, 'circle radius'), col = c(a[1]);
    const s = 2 * r + 4, m = s / 2;
    const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${s}" height="${s}"><circle cx="${m}" cy="${m}" r="${r}" fill="none" stroke="#fff" stroke-width="3"/><circle cx="${m}" cy="${m}" r="${r}" fill="none" stroke="${esc(col)}" stroke-width="1.5"/></svg>`;
    return { css: url(svg, m, m, 'crosshair'), w: s, h: s, hot: [m, m] };
  }
  if (f === 'cross' && a.length === 2) {
    const z = n(a[0], 4, 64, 'cross size'), col = c(a[1]);
    const s = z + 2, m = s / 2;
    const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${s}" height="${s}"><path d="M${m} 1V${s - 1}M1 ${m}H${s - 1}" stroke="#fff" stroke-width="3"/><path d="M${m} 1V${s - 1}M1 ${m}H${s - 1}" stroke="${esc(col)}" stroke-width="1.2"/></svg>`;
    return { css: url(svg, m, m, 'crosshair'), w: s, h: s, hot: [m, m] };
  }
  if (f === 'glyph' && (a.length === 1 || a.length === 3)) {
    const t = String(a[0]);
    if (!t || [...t].length > 3) throw new Error('glyph: one to three characters');
    const s = 32, hx = a.length === 3 ? n(a[1], 0, s, 'hot spot x') : 16, hy = a.length === 3 ? n(a[2], 0, s, 'hot spot y') : 16;
    const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${s}" height="${s}"><text x="16" y="25" font-size="24" text-anchor="middle">${esc(t)}</text></svg>`;
    return { css: url(svg, hx, hy, 'pointer'), w: s, h: s, hot: [hx, hy] };
  }
  if (f === 'svg' && a.length === 3) {
    const t = String(a[0]);
    const w = Number(/width="(\d+)"/.exec(t)?.[1]), h = Number(/height="(\d+)"/.exec(t)?.[1]);
    if (!/^<svg[\s>]/.test(t) || !w || !h || w > MAX || h > MAX) throw new Error(`svg: an <svg> with width and height up to ${MAX}`);
    if (/<script|\son\w+=|href=/i.test(t)) throw new Error('svg: no scripts, events or links');
    const hx = n(a[1], 0, w, 'hot spot x'), hy = n(a[2], 0, h, 'hot spot y');
    const svg = /xmlns=/.test(t) ? t : t.replace('<svg', '<svg xmlns="http://www.w3.org/2000/svg"');
    return { css: url(svg, hx, hy, 'default'), w, h, hot: [hx, hy] };
  }
  throw new Error('a pointer is a name (crosshair, move, ...), circle(R, Colour), cross(Size, Colour), glyph(Text) or svg(Text, X, Y)');
}

export const NAMES = Object.keys(SYSTEM);
