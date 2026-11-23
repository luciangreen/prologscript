// A scene as SVG: what the screen shows and what save_drawing writes. Pure.
import { drawn } from './scene.js';

const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);
const n = (v) => (Math.round(v * 100) / 100).toString();

// one shape as an SVG element: [tag, attributes]
export function element(it) {
  const st = it.style ?? {};
  const paint = { fill: it.kind === 'line' || it.kind === 'path' ? 'none' : st.fill ?? 'none', stroke: st.stroke ?? 'none', 'stroke-width': n(st.width ?? 1) };
  const g = it.g;
  switch (it.kind) {
    case 'rect': return ['rect', { x: n(g[0]), y: n(g[1]), width: n(g[2]), height: n(g[3]), ...paint }];
    case 'ellipse': return ['ellipse', { cx: n(g[0]), cy: n(g[1]), rx: n(g[2]), ry: n(g[3]), ...paint }];
    case 'line': return ['line', { x1: n(g[0]), y1: n(g[1]), x2: n(g[2]), y2: n(g[3]), ...paint, 'stroke-linecap': 'round' }];
    case 'poly': return ['polygon', { points: g.map(([x, y]) => `${n(x)},${n(y)}`).join(' '), ...paint, 'stroke-linejoin': 'round' }];
    case 'path': return ['polyline', { points: g.map(([x, y]) => `${n(x)},${n(y)}`).join(' '), ...paint, 'stroke-linejoin': 'round', 'stroke-linecap': 'round' }];
    case 'text': return ['text', { x: n(g[0]), y: n(g[1]), 'font-size': n(g[2]), 'font-family': 'system-ui, sans-serif', fill: st.fill && st.fill !== 'none' ? st.fill : st.stroke ?? '#222', _text: g[3] }];
    default: return ['g', {}];
  }
}

// the whole scene; groups and layers become <g>s, so other programs keep the structure
export function svg(s, w, h, background = null) {
  const out = [`<svg xmlns="http://www.w3.org/2000/svg" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}">`];
  if (background) out.push(`<rect width="${w}" height="${h}" fill="${esc(background)}"/>`);
  const items = drawn(s);
  let layer = null, groups = [];
  const close = (k) => { while (groups.length > k) { out.push('</g>'); groups.pop(); } };
  for (const it of items) {
    if (it.layer !== layer) { close(0); if (layer !== null) out.push('</g>'); layer = it.layer; out.push(`<g id="${esc(layer)}">`); }
    let k = 0;
    while (k < groups.length && groups[k] === it.groups[k]) k++;
    close(k);
    for (const gid of it.groups.slice(k)) { out.push(`<g id="${esc(gid)}">`); groups.push(gid); }
    const [tag, attrs] = element(it);
    const a = Object.entries(attrs).filter(([key]) => key !== '_text').map(([key, v]) => `${key}="${esc(v)}"`).join(' ');
    out.push(tag === 'text' ? `<text id="${esc(it.id)}" ${a}>${esc(attrs._text)}</text>` : `<${tag} id="${esc(it.id)}" ${a}/>`);
  }
  close(0);
  if (layer !== null) out.push('</g>');
  out.push('</svg>');
  return out.join('\n');
}
