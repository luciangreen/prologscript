import { test } from 'node:test';
import assert from 'node:assert/strict';
import * as S from '../lib/scene.js';
import * as M from '../lib/menu.js';
import * as Pt from '../lib/paint.js';
import { cursor } from '../lib/pointer.js';
import { edit, idle, handles } from '../lib/editor.js';
import { svg } from '../lib/svgout.js';

const scene = () => {
  let s = S.empty();
  s = S.add(s, 'a', 'rect', [0, 0, 20, 20], { fill: '#ff0000' });
  s = S.add(s, 'b', 'ellipse', [50, 50, 10, 10], {});
  s = S.add(s, 'c', 'line', [0, 100, 100, 100], { width: 4 });
  return s;
};

test('groups nest, ungroup restores, and the scene stays well formed', () => {
  let s = S.group(scene(), ['a', 'b'], 'g');
  s = S.group(s, ['g', 'c'], 'street');
  assert.deepEqual(S.outline(s), [['layer1', [['street', [['g', ['a', 'b']], 'c']]]]]);
  assert.ok(S.wellFormed(s));
  assert.equal(S.hit(s, 5, 5), 'street');
  assert.equal(S.hit(s, 5, 5, true), 'a');
  s = S.move(s, 'street', 10, 0);
  assert.deepEqual(s.nodes.a.g, [10, 0, 20, 20]);
  assert.deepEqual(S.bounds(s, 'street'), [10, 0, 100, 100]);
  s = S.ungroup(S.ungroup(s, 'street'), 'g');
  assert.deepEqual(S.outline(s), [['layer1', ['a', 'b', 'c']]]);
  assert.throws(() => S.group(s, ['a', 'nope'], 'h'), /nope isn't there/);
});

test('locked and hidden layers', () => {
  let s = S.addLayer(scene(), 'top', 'Top');
  s = S.add(s, 'd', 'rect', [0, 0, 30, 30], { fill: '#00ff00' });
  assert.equal(S.hit(s, 5, 5), 'd');
  s = S.setLayer(s, 'top', 'shown', false);
  assert.equal(S.hit(s, 5, 5), 'a');
  s = S.setLayer(s, 'layer1', 'locked', true);
  assert.equal(S.hit(s, 5, 5), null);
  for (const f of [() => S.move(s, 'a', 1, 1), () => S.restack(s, 'a', 'front'), () => S.restyle(s, 'a', { fill: 'red' }), () => S.remove(s, 'a')]) assert.throws(f, /locked/);
  assert.equal(S.tree(s)[0].id, 'top');
});

test('resizing scales everything inside a group', () => {
  let s = S.group(scene(), ['a', 'b'], 'g');
  s = S.scaleTo(s, 'g', [0, 0, 120, 120]);
  assert.deepEqual(S.bounds(s, 'g'), [0, 0, 120, 120]);
});

test('the editor selects, moves, resizes and selects with a band', () => {
  let st = idle(), s = scene();
  ({ state: st, scene: s } = edit(st, s, { type: 'down', at: [5, 5] }));
  assert.deepEqual(s.selected, ['a']);
  ({ state: st, scene: s } = edit(st, s, { type: 'drag', at: [15, 10] }));
  ({ state: st, scene: s } = edit(st, s, { type: 'up', at: [15, 10] }));
  assert.deepEqual(s.nodes.a.g, [10, 5, 20, 20]);
  const [, hx, hy] = handles(s).find(([n]) => n === 'se');
  ({ state: st, scene: s } = edit(st, s, { type: 'down', at: [hx, hy] }));
  assert.equal(st.mode, 'resizing');
  ({ state: st, scene: s } = edit(st, s, { type: 'drag', at: [hx + 20, hy + 20] }));
  assert.deepEqual(S.bounds(s, 'a'), [10, 5, 40, 40]);
  ({ state: st, scene: s } = edit(idle(), s, { type: 'down', at: [200, 200] }));
  ({ state: st, scene: s } = edit(st, s, { type: 'drag', at: [-5, -5] }));
  ({ scene: s } = edit(st, s, { type: 'up', at: [-5, -5] }));
  assert.deepEqual(s.selected.sort(), ['a', 'b', 'c']);
});

test('SVG keeps layers and groups', () => {
  const out = svg(S.group(scene(), ['a', 'b'], 'g'), 200, 200);
  assert.match(out, /<g id="layer1">\n<g id="g">\n<rect id="a"/);
  assert.match(out, /<line id="c" [^>]*stroke-width="4"/);
});

test('menus: keys skip separators and disabled items; shortcuts look inside submenus', () => {
  const m = [{ type: 'item', label: 'A', goal: 'a' }, { type: 'sep' }, { type: 'item', label: 'B', goal: 'b', enabled: false },
    { type: 'menu', label: 'More', items: [{ type: 'item', label: 'C', goal: 'c', key: 'k' }] }];
  assert.deepEqual(M.key(m, [0], 'down'), { path: [3] });
  assert.deepEqual(M.key(m, [3], 'right'), { path: [3, 0] });
  assert.deepEqual(M.key(m, [3, 0], 'enter'), { path: [], run: 'c', closed: true });
  assert.equal(M.shortcut(m, 'K'), 'c');
  assert.equal(M.depth(m), 2);
  assert.deepEqual(M.paths(m).map((p) => p.label), ['A', 'B', 'More › C']);
});

test('painting: spray is the same every time; fill and clear', () => {
  assert.deepEqual(Pt.sprayPoints(10, 10, 6, 3), Pt.sprayPoints(10, 10, 6, 3));
  const b = Pt.bitmap(20, 10);
  Pt.apply(b, { op: 'line', x1: 0, y1: 5, x2: 19, y2: 5 }, { colour: 0, size: 1, tip: 'round' });
  Pt.apply(b, { op: 'fill', x: 0, y: 0 }, { colour: 0xff0000, size: 1, tip: 'round' });
  assert.equal(Pt.get(b, 10, 0), 0xff0000);
  assert.equal(Pt.get(b, 10, 9), 0xffffff, 'the line keeps the fill above it');
  assert.equal(Pt.colour('#abc'), 0xaabbcc);
  assert.throws(() => Pt.colour('mauve-ish'), /isn't a colour/);
});

test('pointers: own SVG may not carry scripts', () => {
  assert.equal(cursor('hand').css, 'pointer');
  assert.match(cursor({ f: 'circle', a: [6, 'red'] }).css, /^url\("data:image\/svg\+xml,/);
  assert.throws(() => cursor({ f: 'svg', a: ['<svg width="10" height="10"><script>x</script></svg>', 0, 0] }), /no scripts/);
});
