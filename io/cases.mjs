// prologscript's pure core: the functions whose 200 inputs and outputs are in io/ios.txt and
// io/ios.jsonl. proofs/spec.pl gives the same outputs from its own Prolog model.
import * as S from '../lib/scene.js';
import * as M from '../lib/menu.js';
import * as Pt from '../lib/paint.js';
import { cursor } from '../lib/pointer.js';

export const title = 'PrologScript';

// ---- a script of scene operations, applied to an empty scene; it stops at the first error
const OPS = {
  add: (s, id, kind, g, st) => S.add(s, id, kind, g, st), remove: S.remove, move: S.move, group: S.group, ungroup: S.ungroup,
  restack: S.restack, addLayer: S.addLayer, useLayer: S.useLayer, setLayer: S.setLayer, moveLayer: S.moveLayer, toLayer: S.toLayer, select: S.select
};
export function script(ops) {
  let s = S.empty(), error = null;
  ops.forEach((op, i) => { if (error) return; try { s = OPS[op[0]](s, ...op.slice(1)); } catch (e) { error = { at: i, message: e.message }; } });
  return {
    outline: S.outline(s),
    layers: s.layers.map((l) => [l.id, l.name, l.shown, l.locked]),
    active: s.active,
    selected: s.selected,
    shapes: Object.values(s.nodes).filter((n) => n.kind !== 'group').map((n) => [n.id, n.kind, n.g]).sort((a, b) => (a[0] < b[0] ? -1 : 1)),
    ...(error ? { error } : {})
  };
}
const build = (ops) => { let s = S.empty(); for (const op of ops) try { s = OPS[op[0]](s, ...op.slice(1)); } catch { /* skipped */ } return s; };

const IDS = ['a', 'b', 'c', 'd', 'e', 'f', 'g1', 'g2', 'Bad', 'layer1'];
const KINDS = ['rect', 'rect', 'ellipse', 'line', 'poly', 'path', 'text'];
const geom = (rnd, kind, bad) => {
  const n = () => rnd.int(0, 60);
  switch (kind) {
    case 'rect': case 'ellipse': return bad ? [n(), n(), -5, 4] : [n(), n(), rnd.int(0, 30), rnd.int(0, 30)];
    case 'line': return [n(), n(), n(), n()];
    case 'poly': case 'path': return bad ? [[n(), n()]] : Array.from({ length: rnd.int(2, 5) }, () => [n(), n()]);
    case 'text': return [n(), n(), bad ? 0 : rnd.pick([10, 20]), rnd.pick(['Hi', 'Hello there', 'x'])];
    default: return [n()];
  }
};
const style = (rnd) => (rnd.chance(0.6) ? { fill: rnd.pick(['none', '#e53935', '#81d4fa']), width: rnd.pick([1, 2, 6, 12]) } : {});
// an operation on the scene as it is: about one in sixteen is wrong on purpose
function op(rnd, s) {
  const bad = rnd.chance(0.06);
  const ids = Object.keys(s.nodes), tops = s.layers.flatMap((l) => l.items), groups = ids.filter((i) => s.nodes[i].kind === 'group');
  const some = (xs) => (xs.length ? rnd.pick(xs) : 'a');
  const fresh = (pre) => { for (let k = 1; ; k++) if (!s.nodes[`${pre}${k}`] && !s.layers.some((l) => l.id === `${pre}${k}`)) return `${pre}${k}`; };
  const k = ids.length < 2 ? 'add' : rnd.pick(['add', 'add', 'add', 'add', 'add', 'remove', 'move', 'move', 'group', 'group', 'ungroup', 'restack', 'restack', 'addLayer', 'useLayer', 'setLayer', 'moveLayer', 'toLayer', 'select', 'select']);
  switch (k) {
    case 'add': {
      const kind = bad && rnd.chance(0.3) ? 'blob' : rnd.pick(KINDS);
      const id = bad && rnd.chance(0.5) ? rnd.pick(['Bad', ids[0] ?? 'Bad', '9x']) : fresh(rnd.pick(['s', 'box', 'dot']));
      return ['add', id, kind, geom(rnd, kind, bad), style(rnd)];
    }
    case 'remove': case 'move': { const id = bad ? 'nope' : some(ids); return k === 'remove' ? ['remove', id] : ['move', id, rnd.int(-20, 20), rnd.int(-20, 20)]; }
    case 'group': {
      // siblings: some items of one layer or one group; a wrong one mixes places or repeats
      const lists = [...s.layers.map((l) => l.items), ...groups.map((g) => s.nodes[g].items)].filter((l) => l.length);
      const pool = lists.length ? rnd.pick(lists) : ['a'];
      let pick = [...new Set(rnd.some(pool, 1, 3))];
      if (bad) pick = rnd.chance(0.5) ? [...pick, pick[0]] : [...pick, some(tops.filter((t) => !pool.includes(t))) ];
      return ['group', pick, bad && rnd.chance(0.3) ? 'G' : fresh('g')];
    }
    case 'ungroup': return ['ungroup', bad ? some(ids.filter((i) => s.nodes[i].kind !== 'group')) : some(groups)];
    case 'restack': return ['restack', bad ? 'nope' : some(ids), rnd.pick(['raise', 'lower', 'front', 'back'])];
    case 'addLayer': return ['addLayer', bad ? rnd.pick(['layer1', 'Top']) : fresh('layer'), rnd.pick(['Top', 'Middle', ''])];
    case 'useLayer': return ['useLayer', bad ? 'nope' : rnd.pick(s.layers).id];
    case 'moveLayer': return ['moveLayer', rnd.pick(s.layers).id, rnd.pick(['raise', 'lower'])];
    case 'setLayer': return ['setLayer', rnd.pick(s.layers).id, rnd.pick(['shown', 'locked']), rnd.chance(bad ? 0.5 : 0.25)];
    case 'toLayer': return ['toLayer', bad ? some(ids) : some(tops), rnd.pick(s.layers).id];
    default: return ['select', bad ? ['nope'] : [...new Set(rnd.some(ids.length ? ids : ['a'], 0, 3))]];
  }
}
const makeScript = (rnd, lo, hi) => {
  let s = S.empty();
  return Array.from({ length: rnd.int(lo, hi) }, () => { const o = op(rnd, s); try { s = OPS[o[0]](s, ...o.slice(1)); } catch { /* the script will stop here */ } return o; });
};

// ---- menus
const LABELS = ['File', 'Edit', 'Colour', 'Warm', 'Red', 'Blue', 'Size', 'Undo'];
function menu(rnd, depth = 0) {
  return Array.from({ length: rnd.int(1, 4) }, () => {
    const r = rnd.next();
    if (r < 0.15) return { type: 'sep' };
    if (r < 0.4 && depth < 2) return { type: 'menu', label: rnd.pick(LABELS), items: menu(rnd, depth + 1), ...(rnd.chance(0.1) ? { enabled: false } : {}) };
    return { type: 'item', label: rnd.pick(LABELS), goal: `go(${rnd.int(1, 99)})`, ...(rnd.chance(0.4) ? { key: rnd.pick(['a', 'b', 'Z', 'z']) } : {}), ...(rnd.chance(0.15) ? { enabled: false } : {}) };
  });
}
const pathIn = (rnd, m) => { const p = []; let items = m; while (items?.length && rnd.chance(0.7)) { const i = rnd.int(0, items.length - 1); p.push(i); items = items[i]?.type === 'menu' ? items[i].items : null; } return p; };

// ---- painting
const grid = (rnd, w, h, colours) => Array.from({ length: h }, () => Array.from({ length: w }, () => rnd.int(0, colours - 1)));
function fillGrid(rows, x, y, c) {
  const h = rows.length, w = rows[0].length;
  const b = { w, h, px: rows.flat() };
  Pt.fillRegion(b, x, y, c, { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity });
  return Array.from({ length: h }, (_, j) => b.px.slice(j * w, j * w + w));
}
function dotGrid(w, h, x, y, size, tip) {
  const b = Pt.bitmap(w, h, 0);
  Pt.apply(b, { op: 'dot', x, y }, { colour: 1, size, tip });
  return Array.from({ length: h }, (_, j) => [...b.px.slice(j * w, j * w + w)]);
}

export const cases = [
  { name: 'script', run: script, make: (rnd) => [makeScript(rnd, 3, 9)] },
  { name: 'script', run: script, make: (rnd) => [makeScript(rnd, 6, 14)] },
  {
    name: 'hit', run: (ops, x, y) => { const s = build(ops); return { top: S.hit(s, x, y), deep: S.hit(s, x, y, true) }; },
    make: (rnd) => {
      const ops = makeScript(rnd, 4, 12), sc = build(ops), ids = Object.keys(sc.nodes);
      if (!ids.length || rnd.chance(0.25)) return [ops, rnd.int(-5, 70), rnd.int(-5, 70)];
      const [x, y, w, h] = S.bounds(sc, rnd.pick(ids)); // a point in (or by) a shape's box
      return [ops, Math.round(x + rnd.next() * w), Math.round(y + rnd.next() * h)];
    }
  },
  { name: 'bounds', run: (ops, id) => S.bounds(build(ops), id), make: (rnd) => { const ops = makeScript(rnd, 2, 9); const ids = Object.keys(build(ops).nodes); return [ops, ids.length && rnd.chance(0.9) ? rnd.pick(ids) : 'nope']; } },
  { name: 'menuKey', run: (m, p, k) => M.key(m, p, k), make: (rnd) => { const m = menu(rnd); return [m, pathIn(rnd, m), rnd.pick(['up', 'down', 'left', 'right', 'enter', 'escape', 'tab'])]; } },
  { name: 'menuChoose', run: (m, p) => M.choose(m, p), make: (rnd) => { const m = menu(rnd); const p = pathIn(rnd, m); return [m, p.length ? p : [0]]; } },
  { name: 'shortcut', run: (m, k) => M.shortcut(m, k), make: (rnd) => [menu(rnd), rnd.pick(['a', 'A', 'b', 'z', 'q'])] },
  { name: 'line', run: Pt.linePoints, make: (rnd) => [rnd.int(-6, 6), rnd.int(-6, 6), rnd.int(-6, 6), rnd.int(-6, 6)] },
  { name: 'fill', run: fillGrid, make: (rnd) => { const w = rnd.int(1, 6), h = rnd.int(1, 5); return [grid(rnd, w, h, rnd.int(1, 3)), rnd.int(-1, w), rnd.int(-1, h), rnd.int(0, 2)]; } },
  { name: 'dot', run: dotGrid, make: (rnd) => [rnd.int(3, 9), rnd.int(3, 7), rnd.int(-1, 8), rnd.int(-1, 6), rnd.int(1, 7), rnd.pick(['round', 'square'])] },
  {
    name: 'cursor', run: (spec) => { const c = cursor(spec); return { w: c.w, h: c.h, hot: c.hot }; },
    make: (rnd) => [rnd.pick([
      () => rnd.pick(['crosshair', 'hand', 'arrow', 'pencil', 'none']),
      () => ({ f: 'circle', a: [rnd.pick([0, 1, 7, 7.6, 60, 61]), rnd.pick(['red', '#ff8800', '#abc', 'not a colour', 12])] }),
      () => ({ f: 'cross', a: [rnd.pick([3, 4, 9, 64, 65]), rnd.pick(['blue', '#123456'])] }),
      () => ({ f: 'glyph', a: rnd.chance(0.5) ? [rnd.pick(['⭐', 'ab', 'abcd', ''])] : [rnd.pick(['✏', 'x']), rnd.int(-1, 33), rnd.int(0, 32)] }),
      () => ({ f: 'svg', a: [rnd.pick(['<svg width="20" height="20"><circle r="5"/></svg>', '<svg width="200" height="20"></svg>', '<div width="2" height="2">', '<svg width="20" height="20" onload="x()"></svg>', '<svg height="9"></svg>']), rnd.int(0, 22), rnd.int(0, 22)] }),
      () => ({ f: 'blob', a: [] })
    ])()]
  }
];
