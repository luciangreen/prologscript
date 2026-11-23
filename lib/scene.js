// The vector scene: shapes, groups (to any depth) and layers (levels), in stacking order.
// Pure: every operation takes a scene and returns a new one, or throws an Error whose message
// is shown to the user. proofs/spec.pl states the same operations in Prolog.
//
// A scene: { layers: [Layer bottom..top], nodes: { id: Node }, active: layerId, selected: [id], n }
//   Layer: { id, name, shown, locked, items: [id bottom..top] }
//   Node:  { id, kind: 'rect'|'ellipse'|'line'|'poly'|'path'|'text'|'group', g: geometry, style, items? }
// Geometry: rect [x,y,w,h]; ellipse [cx,cy,rx,ry]; line [x1,y1,x2,y2]; poly/path [[x,y],..]; text [x,y,size,"text"]
// Style: { fill, stroke, width } (colours as text)

export const KINDS = ['rect', 'ellipse', 'line', 'poly', 'path', 'text'];
export const DEFAULT_STYLE = Object.freeze({ fill: 'none', stroke: '#222222', width: 2 });

export function empty() {
  return { layers: [{ id: 'layer1', name: 'Layer 1', shown: true, locked: false, items: [] }], nodes: {}, active: 'layer1', selected: [], n: 0 };
}

const fail = (m) => { throw new Error(m); };
const clone = (s) => ({ ...s, layers: s.layers.map((l) => ({ ...l, items: [...l.items] })), nodes: { ...s.nodes }, selected: [...s.selected] });
const ID = /^[a-z][A-Za-z0-9_]{0,39}$/;
const num = (v) => typeof v === 'number' && Number.isFinite(v);

// where an item lives: its layer and its parent's item list (a layer's or a group's)
export function parentOf(s, id) {
  for (const l of s.layers) {
    if (l.items.includes(id)) return { layer: l.id, parent: null };
  }
  for (const n of Object.values(s.nodes)) if (n.kind === 'group' && n.items.includes(id)) return { layer: layerOf(s, n.id), parent: n.id };
  return null;
}
export function layerOf(s, id) {
  const p = parentOf(s, id);
  return p ? p.layer : null;
}
const siblings = (s, p) => (p.parent ? s.nodes[p.parent].items : s.layers.find((l) => l.id === p.layer).items);

// a shape term's geometry, checked
export function geometry(kind, g) {
  const ok =
    kind === 'rect' || kind === 'ellipse' ? Array.isArray(g) && g.length === 4 && g.every(num) && g[2] >= 0 && g[3] >= 0
    : kind === 'line' ? Array.isArray(g) && g.length === 4 && g.every(num)
    : kind === 'poly' || kind === 'path' ? Array.isArray(g) && g.length >= 2 && g.every((p) => Array.isArray(p) && p.length === 2 && p.every(num))
    : kind === 'text' ? Array.isArray(g) && g.length === 4 && num(g[0]) && num(g[1]) && num(g[2]) && g[2] > 0 && typeof g[3] === 'string'
    : false;
  if (!ok) fail(`${kind}: not a shape I can draw`);
  return kind === 'poly' || kind === 'path' ? g.map((p) => [p[0], p[1]]) : [...g];
}
export function style(st = {}) {
  const out = { ...DEFAULT_STYLE };
  for (const [k, v] of Object.entries(st)) {
    if (k === 'width') { if (!num(v) || v < 0 || v > 200) fail('width: 0 to 200'); out.width = v; }
    else if (k === 'fill' || k === 'stroke') { if (typeof v !== 'string' || v.length > 40) fail(`${k}: a colour`); out[k] = v; }
    else fail(`style: ${k} isn't fill, stroke or width`);
  }
  return out;
}

export function add(s0, id, kind, g, st) {
  if (!ID.test(id)) fail(`${id}: a name starts with a small letter`);
  if (s0.nodes[id] || s0.layers.some((l) => l.id === id)) fail(`${id} is already there`);
  if (!KINDS.includes(kind)) fail(`${kind} isn't a shape`);
  const s = clone(s0);
  const layer = s.layers.find((l) => l.id === s.active);
  if (layer.locked) fail(`${layer.name} is locked`);
  s.nodes[id] = { id, kind, g: geometry(kind, g), style: style(st) };
  layer.items.push(id);
  s.n = s0.n + 1;
  return s;
}

// every id in an item, itself included (a group's members to any depth)
export function within(s, id) {
  const n = s.nodes[id];
  if (!n) return [];
  return n.kind === 'group' ? [id, ...n.items.flatMap((c) => within(s, c))] : [id];
}

export function remove(s0, id) {
  const p = parentOf(s0, id) ?? fail(`${id} isn't there`);
  if (s0.layers.find((l) => l.id === p.layer).locked) fail(`${id} is on a locked layer`);
  const s = clone(s0);
  const gone = within(s0, id);
  const list = siblings(s, p);
  if (p.parent) s.nodes[p.parent] = { ...s.nodes[p.parent], items: list.filter((x) => x !== id) };
  else s.layers.find((l) => l.id === p.layer).items = list.filter((x) => x !== id);
  for (const g of gone) delete s.nodes[g];
  s.selected = s.selected.filter((x) => !gone.includes(x));
  return s;
}

const shift = (n, dx, dy) => {
  const g = n.g;
  switch (n.kind) {
    case 'rect': case 'ellipse': return { ...n, g: [g[0] + dx, g[1] + dy, g[2], g[3]] };
    case 'line': return { ...n, g: [g[0] + dx, g[1] + dy, g[2] + dx, g[3] + dy] };
    case 'poly': case 'path': return { ...n, g: g.map(([x, y]) => [x + dx, y + dy]) };
    case 'text': return { ...n, g: [g[0] + dx, g[1] + dy, g[2], g[3]] };
    default: return n;
  }
};
export function move(s0, id, dx, dy) {
  if (!num(dx) || !num(dy)) fail('move: by numbers');
  const p = parentOf(s0, id) ?? fail(`${id} isn't there`);
  if (s0.layers.find((l) => l.id === p.layer).locked) fail(`${id} is on a locked layer`);
  const s = clone(s0);
  for (const x of within(s0, id)) s.nodes[x] = shift(s.nodes[x], dx, dy);
  return s;
}

const unlocked = (s, id) => { if (s.layers.find((l) => l.id === layerOf(s, id))?.locked) fail(`${id} is on a locked layer`); };
export function restyle(s0, id, st) {
  const n = s0.nodes[id] ?? fail(`${id} isn't there`);
  unlocked(s0, id);
  const s = clone(s0);
  for (const x of within(s0, id)) if (s.nodes[x].kind !== 'group') s.nodes[x] = { ...s.nodes[x], style: style({ ...s.nodes[x].style, ...st }) };
  return n ? s : s0;
}
export function reshape(s0, id, kind, g) {
  const n = s0.nodes[id] ?? fail(`${id} isn't there`);
  if (n.kind === 'group') fail(`${id} is a group`);
  if (!KINDS.includes(kind)) fail(`${kind} isn't a shape`);
  unlocked(s0, id);
  const s = clone(s0);
  s.nodes[id] = { ...n, kind, g: geometry(kind, g) };
  return s;
}

// group items that share a parent; the group takes the place of the topmost of them
export function group(s0, ids, gid) {
  if (!ID.test(gid)) fail(`${gid}: a name starts with a small letter`);
  if (s0.nodes[gid]) fail(`${gid} is already there`);
  if (!Array.isArray(ids) || ids.length < 1) fail('group: which items?');
  if (new Set(ids).size !== ids.length) fail('group: an item is named twice');
  const ps = ids.map((id) => parentOf(s0, id) ?? fail(`${id} isn't there`));
  if (!ps.every((p) => p.layer === ps[0].layer && p.parent === ps[0].parent)) fail('group: the items must be side by side (in the same layer or group)');
  if (s0.layers.find((l) => l.id === ps[0].layer).locked) fail('group: the layer is locked');
  const s = clone(s0);
  const list = siblings(s, ps[0]);
  const members = list.filter((x) => ids.includes(x)); // in stacking order
  const top = Math.max(...members.map((x) => list.indexOf(x)));
  const at = top - (members.length - 1);
  const rest = list.filter((x) => !ids.includes(x));
  rest.splice(at, 0, gid);
  s.nodes[gid] = { id: gid, kind: 'group', items: members };
  if (ps[0].parent) s.nodes[ps[0].parent] = { ...s.nodes[ps[0].parent], items: rest };
  else s.layers.find((l) => l.id === ps[0].layer).items = rest;
  s.selected = s.selected.filter((x) => !ids.includes(x));
  return s;
}

// the group's items take its place, in order
export function ungroup(s0, gid) {
  const n = s0.nodes[gid] ?? fail(`${gid} isn't there`);
  if (n.kind !== 'group') fail(`${gid} isn't a group`);
  const p = parentOf(s0, gid);
  if (s0.layers.find((l) => l.id === p.layer).locked) fail('ungroup: the layer is locked');
  const s = clone(s0);
  const list = siblings(s, p);
  const i = list.indexOf(gid);
  const out = [...list.slice(0, i), ...n.items, ...list.slice(i + 1)];
  if (p.parent) s.nodes[p.parent] = { ...s.nodes[p.parent], items: out };
  else s.layers.find((l) => l.id === p.layer).items = out;
  delete s.nodes[gid];
  s.selected = s.selected.filter((x) => x !== gid);
  return s;
}

// stacking within a parent: up one, down one, to the front, to the back
export function restack(s0, id, how) {
  const p = parentOf(s0, id) ?? fail(`${id} isn't there`);
  if (s0.layers.find((l) => l.id === p.layer).locked) fail(`${id} is on a locked layer`);
  const s = clone(s0);
  const list = siblings(s, p);
  const i = list.indexOf(id);
  const j = how === 'raise' ? Math.min(list.length - 1, i + 1) : how === 'lower' ? Math.max(0, i - 1) : how === 'front' ? list.length - 1 : how === 'back' ? 0 : fail(`${how}: raise, lower, front or back`);
  list.splice(i, 1);
  list.splice(j, 0, id);
  if (p.parent) s.nodes[p.parent] = { ...s.nodes[p.parent], items: list };
  else s.layers.find((l) => l.id === p.layer).items = list;
  return s;
}

export function addLayer(s0, id, name) {
  if (!ID.test(id)) fail(`${id}: a name starts with a small letter`);
  if (s0.nodes[id] || s0.layers.some((l) => l.id === id)) fail(`${id} is already there`);
  const s = clone(s0);
  s.layers.push({ id, name: String(name).slice(0, 40) || id, shown: true, locked: false, items: [] });
  s.active = id;
  return s;
}
export function renameLayer(s0, id, name) {
  const s = clone(s0);
  const l = s.layers.find((x) => x.id === id) ?? fail(`${id} isn't a layer`);
  l.name = String(name).slice(0, 40) || id;
  return s;
}
export function useLayer(s0, id) {
  if (!s0.layers.some((l) => l.id === id)) fail(`${id} isn't a layer`);
  return { ...clone(s0), active: id };
}
export function setLayer(s0, id, key, value) {
  if (!['shown', 'locked'].includes(key) || typeof value !== 'boolean') fail('a layer is shown or locked: true or false');
  const s = clone(s0);
  const l = s.layers.find((x) => x.id === id) ?? fail(`${id} isn't a layer`);
  l[key] = value;
  if (key === 'shown' && !value || key === 'locked' && value) s.selected = s.selected.filter((x) => layerOf(s, x) !== id);
  return s;
}
export function moveLayer(s0, id, how) {
  const s = clone(s0);
  const i = s.layers.findIndex((l) => l.id === id);
  if (i < 0) fail(`${id} isn't a layer`);
  const j = how === 'raise' ? Math.min(s.layers.length - 1, i + 1) : how === 'lower' ? Math.max(0, i - 1) : fail(`${how}: raise or lower`);
  const [l] = s.layers.splice(i, 1);
  s.layers.splice(j, 0, l);
  return s;
}
// a top-level item (and all it holds) to the top of another layer
export function toLayer(s0, id, lid) {
  const p = parentOf(s0, id) ?? fail(`${id} isn't there`);
  if (p.parent) fail(`${id} is inside ${p.parent}: ungroup it first`);
  const to = s0.layers.find((l) => l.id === lid) ?? fail(`${lid} isn't a layer`);
  if (to.locked || s0.layers.find((l) => l.id === p.layer).locked) fail('a locked layer');
  if (p.layer === lid) return s0;
  const s = clone(s0);
  const from = s.layers.find((l) => l.id === p.layer);
  from.items = from.items.filter((x) => x !== id);
  s.layers.find((l) => l.id === lid).items.push(id);
  return s;
}
export function removeLayer(s0, id) {
  if (s0.layers.length === 1) fail("the last layer can't go");
  const l = s0.layers.find((x) => x.id === id) ?? fail(`${id} isn't a layer`);
  let s = s0;
  for (const it of [...l.items]) s = remove(setLayer(s, id, 'locked', false), it);
  s = clone(s);
  s.layers = s.layers.filter((x) => x.id !== id);
  if (s.active === id) s.active = s.layers[s.layers.length - 1].id;
  return s;
}

export function select(s0, ids) {
  for (const id of ids) if (!s0.nodes[id]) fail(`${id} isn't there`);
  return { ...clone(s0), selected: [...new Set(ids)] };
}

// ---- looking

export function bounds(s, id) {
  const n = s.nodes[id];
  if (!n) fail(`${id} isn't there`);
  if (n.kind === 'group') {
    const bs = n.items.map((c) => bounds(s, c));
    if (!bs.length) return [0, 0, 0, 0];
    const x0 = Math.min(...bs.map((b) => b[0])), y0 = Math.min(...bs.map((b) => b[1]));
    const x1 = Math.max(...bs.map((b) => b[0] + b[2])), y1 = Math.max(...bs.map((b) => b[1] + b[3]));
    return [x0, y0, x1 - x0, y1 - y0];
  }
  const g = n.g;
  switch (n.kind) {
    case 'rect': return [...g];
    case 'ellipse': return [g[0] - g[2], g[1] - g[3], 2 * g[2], 2 * g[3]];
    case 'line': return [Math.min(g[0], g[2]), Math.min(g[1], g[3]), Math.abs(g[2] - g[0]), Math.abs(g[3] - g[1])];
    case 'poly': case 'path': {
      const xs = g.map((p) => p[0]), ys = g.map((p) => p[1]);
      return [Math.min(...xs), Math.min(...ys), Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)];
    }
    case 'text': return [g[0], g[1] - g[2], textWidth(g[3], g[2]), g[2] * 1.25];
    default: return [0, 0, 0, 0];
  }
}
export const textWidth = (t, size) => Math.round(t.length * size * 0.6);

const segDist2 = (px, py, x1, y1, x2, y2) => {
  const dx = x2 - x1, dy = y2 - y1;
  const L = dx * dx + dy * dy;
  const t = L === 0 ? 0 : Math.max(0, Math.min(1, ((px - x1) * dx + (py - y1) * dy) / L));
  const qx = x1 + t * dx - px, qy = y1 + t * dy - py;
  return qx * qx + qy * qy;
};
const inPoly = (x, y, pts) => {
  let inside = false;
  for (let i = 0, j = pts.length - 1; i < pts.length; j = i++) {
    const [xi, yi] = pts[i], [xj, yj] = pts[j];
    if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) inside = !inside;
  }
  return inside;
};
// does a shape cover the point? (the edge counts, with a little slack to tap thin lines)
export function covers(n, x, y) {
  const g = n.g, slack = Math.max(4, (n.style?.width ?? 2) / 2 + 3), s2 = slack * slack;
  const filled = n.style && n.style.fill !== 'none';
  switch (n.kind) {
    case 'rect': {
      const [rx, ry, w, h] = g;
      if (filled) return x >= rx && x <= rx + w && y >= ry && y <= ry + h;
      return x >= rx - slack && x <= rx + w + slack && y >= ry - slack && y <= ry + h + slack &&
        !(x > rx + slack && x < rx + w - slack && y > ry + slack && y < ry + h - slack);
    }
    case 'ellipse': {
      const [cx, cy, rx, ry] = g;
      if (rx === 0 || ry === 0) return false;
      const d = ((x - cx) / rx) ** 2 + ((y - cy) / ry) ** 2;
      if (filled) return d <= 1;
      const r = Math.sqrt(d), m = Math.min(rx, ry);
      return Math.abs(r - 1) * m <= slack;
    }
    case 'line': return segDist2(x, y, ...g) <= s2;
    case 'poly':
      if (filled && inPoly(x, y, g)) return true;
      return g.some((p, i) => segDist2(x, y, ...p, ...g[(i + 1) % g.length]) <= s2);
    case 'path': return g.slice(1).some((p, i) => segDist2(x, y, ...g[i], ...p) <= s2);
    case 'text': { const [bx, by, bw, bh] = bounds({ nodes: { t: n } }, 't'); return x >= bx && x <= bx + bw && y >= by && y <= by + bh; }
    default: return false;
  }
}

// the item under a point: the topmost, in a shown and unlocked layer. top: the outermost group
// holding it (what a click selects); deep: the shape itself.
export function hit(s, x, y, deep = false) {
  for (let li = s.layers.length - 1; li >= 0; li--) {
    const l = s.layers[li];
    if (!l.shown || l.locked) continue;
    for (let i = l.items.length - 1; i >= 0; i--) {
      const found = hitIn(s, l.items[i], x, y);
      if (found) return deep ? found : l.items[i];
    }
  }
  return null;
}
function hitIn(s, id, x, y) {
  const n = s.nodes[id];
  if (n.kind === 'group') {
    for (let i = n.items.length - 1; i >= 0; i--) { const f = hitIn(s, n.items[i], x, y); if (f) return f; }
    return null;
  }
  return covers(n, x, y) ? id : null;
}

// everything drawn, bottom to top: [{ id, kind, g, style, layer, depth, groups: [outer..inner] }]
export function drawn(s) {
  const out = [];
  const walk = (id, layer, groups) => {
    const n = s.nodes[id];
    if (n.kind === 'group') { for (const c of n.items) walk(c, layer, [...groups, id]); return; }
    out.push({ id, kind: n.kind, g: n.g, style: n.style, layer, groups });
  };
  for (const l of s.layers) if (l.shown) for (const id of l.items) walk(id, l.id, []);
  return out;
}

// the tree the layers panel shows: [{ id, name|kind, shown, locked, active, items: [ { id, kind, items? } ] }]
export function tree(s) {
  const node = (id) => { const n = s.nodes[id]; return n.kind === 'group' ? { id, kind: 'group', items: n.items.map(node) } : { id, kind: n.kind }; };
  return [...s.layers].reverse().map((l) => ({ id: l.id, name: l.name, shown: l.shown, locked: l.locked, active: l.id === s.active, items: [...l.items].reverse().map(node) }));
}

// a fresh id: prefix + the next number not taken
export function newId(s, prefix = 'shape') {
  if (!/^[a-z][a-z_]{0,20}$/.test(prefix)) fail(`${prefix}: small letters`);
  for (let k = 1; ; k++) { const id = `${prefix}${k}`; if (!s.nodes[id] && !s.layers.some((l) => l.id === id)) return id; }
}

// a check that a scene is well formed: every node is in exactly one place; groups hold only nodes
export function wellFormed(s) {
  const seen = new Map();
  const note = (id) => seen.set(id, (seen.get(id) || 0) + 1);
  for (const l of s.layers) l.items.forEach(note);
  for (const n of Object.values(s.nodes)) if (n.kind === 'group') n.items.forEach(note);
  const ids = Object.keys(s.nodes);
  return ids.every((id) => seen.get(id) === 1) && [...seen.keys()].every((id) => s.nodes[id]) && s.layers.some((l) => l.id === s.active) &&
    s.selected.every((id) => s.nodes[id]) && !hasCycle(s);
}
function hasCycle(s) {
  const state = new Map();
  const visit = (id) => { if (state.get(id) === 1) return true; if (state.get(id) === 2) return false; state.set(id, 1); const n = s.nodes[id]; const c = n.kind === 'group' && n.items.some(visit); state.set(id, 2); return c; };
  return Object.keys(s.nodes).some(visit);
}

// what a scene looks like, briefly: [[layer, [items as nested lists]]] (used by the i/os and proofs)
export function outline(s) {
  const node = (id) => { const n = s.nodes[id]; return n.kind === 'group' ? [id, n.items.map(node)] : id; };
  return s.layers.map((l) => [l.id, l.items.map(node)]);
}

// resize an item to new bounds [x, y, w, h]: every point is mapped from its old bounds
export function scaleTo(s0, id, nb) {
  const p = parentOf(s0, id) ?? fail(`${id} isn't there`);
  if (s0.layers.find((l) => l.id === p.layer).locked) fail(`${id} is on a locked layer`);
  if (!Array.isArray(nb) || nb.length !== 4 || !nb.every(num) || nb[2] < 1 || nb[3] < 1) fail('resize: to a box at least 1 by 1');
  const [ox, oy, ow, oh] = bounds(s0, id);
  const sx = ow === 0 ? 1 : nb[2] / ow, sy = oh === 0 ? 1 : nb[3] / oh;
  const X = (x) => nb[0] + (x - ox) * sx, Y = (y) => nb[1] + (y - oy) * sy;
  const s = clone(s0);
  for (const x of within(s0, id)) {
    const n = s.nodes[x], g = n.g;
    if (n.kind === 'group') continue;
    let g2;
    switch (n.kind) {
      case 'rect': g2 = [X(g[0]), Y(g[1]), g[2] * sx, g[3] * sy]; break;
      case 'ellipse': g2 = [X(g[0]), Y(g[1]), g[2] * sx, g[3] * sy]; break;
      case 'line': g2 = [X(g[0]), Y(g[1]), X(g[2]), Y(g[3])]; break;
      case 'poly': case 'path': g2 = g.map(([a, b]) => [X(a), Y(b)]); break;
      case 'text': { const size = Math.max(4, g[2] * sy); g2 = [X(g[0]), Y(g[1] - g[2]) + size, size, g[3]]; break; }
      default: g2 = g;
    }
    s.nodes[x] = { ...n, g: g2.map ? g2.map((v) => (Array.isArray(v) ? v.map(round2) : typeof v === 'number' ? round2(v) : v)) : g2 };
  }
  return s;
}
const round2 = (v) => Math.round(v * 100) / 100;
