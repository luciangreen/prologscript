import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { createRequire } from 'node:module';
import { Runtime } from '../lib/runtime.js';
import { TUTES, parseTute } from '../lib/tutes.js';

createRequire(import.meta.url)('../vendor/pl2detlog.js');
const P = globalThis.PL2D;
const file = (f) => fs.readFileSync(new URL(`../${f}`, import.meta.url), 'utf8');
const ev = (rt, e) => { const m = /\((-?\d+),\s*(-?\d+)/.exec(e); return rt.event(e, m ? { x: +m[1], y: +m[2] } : {}); };
const choose = (rt, which, labels) => {
  let items = rt.menu(which);
  for (const l of labels.slice(0, -1)) items = items.find((e) => e.label === l).items;
  const it = items.find((e) => e.label === labels.at(-1));
  assert.ok(it, `menu entry ${labels.join(' › ')}`);
  return rt.run(it.goal);
};

test('Paint: strokes, nested menus, the palette, fill, eraser and undo', () => {
  const rt = new Runtime(P);
  assert.equal(rt.load(file('demos/paint.pl')).error, null);
  for (const e of ['down(100, 100)', 'drag(200, 150)', 'up(200, 150)']) assert.equal(ev(rt, e).error, null);
  assert.equal(choose(rt, 'context', ['Colour', 'Warm', 'Red']).error, null);
  assert.equal(rt.brush.colour, 0xe53935);
  assert.ok(rt.menu('bar').find((m) => m.label === 'Colour').items[0].items.find((i) => i.label === 'Red').checked);
  ev(rt, 'drop(swatch(green), 5, 5)');
  assert.equal(rt.bitmap.px[0], 0x43a047);
  rt.run('undo');
  assert.equal(rt.bitmap.px[0], 0xffffff);
  choose(rt, 'bar', ['Brush', 'Eraser']);
  ev(rt, 'down(100, 100)'); ev(rt, 'up(100, 100)');
  assert.equal(rt.bitmap.px[100 * 900 + 100], 0xffffff);
});

test('Draw: tools, the palette, groups, styles, layers and the pop-up', () => {
  const rt = new Runtime(P);
  assert.equal(rt.load(file('demos/draw.pl')).error, null);
  rt.run('use_tool(rect)');
  ev(rt, 'down(100, 100)'); ev(rt, 'drag(200, 180)'); ev(rt, 'up(200, 180)');
  assert.deepEqual(rt.scene.nodes.rect1.g, [100, 100, 100, 80]);
  assert.equal(ev(rt, 'drop(house, 500, 300)').error, null);
  assert.equal(rt.scene.nodes.house1.kind, 'group');
  rt.run('use_tool(select)');
  ev(rt, 'down(150, 140)'); ev(rt, 'drag(170, 150)'); ev(rt, 'up(170, 150)');
  assert.deepEqual(rt.scene.selected, ['rect1']);
  choose(rt, 'context', ['Style', 'Fill', 'Warm', 'Orange']);
  assert.equal(rt.scene.nodes.rect1.style.fill, '#fb8c00');
  rt.run('select_all'); choose(rt, 'context', ['Arrange', 'Group', 'Group']);
  assert.equal(rt.scene.selected.length, 1);
  assert.equal(rt.menu('context').find((m) => m.label === 'Arrange').items.find((m) => m.label === 'Group').items.find((i) => i.label === 'Ungroup').enabled, true);
  choose(rt, 'bar', ['Layer', 'New layer']);
  assert.equal(rt.scene.layers.length, 3);
  const moveTo = rt.menu('bar').find((m) => m.label === 'Layer').items.find((m) => m.label === 'Move selection to').items;
  assert.deepEqual(moveTo.map((i) => i.label), ['Layer 3', 'Front', 'Back']);
  rt.run(moveTo[2].goal);
  assert.equal(rt.scene.layers[0].items.length, 3);
  const r = ev(rt, 'right(5, 5)');
  assert.deepEqual(rt.requests.pop(), { popup: 'context', at: [5, 5] });
  assert.match(r.commands.at(-1), /^popup\(context\)/);
});

test('errors show, and an event with no clause does nothing', () => {
  const rt = new Runtime(P);
  rt.load('on(key(a)) :- shape(x, rect(0, 0, 5, 5)), shape(x, rect(1, 1, 5, 5)).\non(key(b)) :- shape(y, rect(0, 0, X, 5)).');
  assert.equal(ev(rt, 'key(a)').error, 'x is already there');
  assert.match(ev(rt, 'key(b)').error, /rect: not a shape I can draw/);
  const r = ev(rt, 'key(z)');
  assert.equal(r.error, null);
  assert.equal(r.handled, false);
  assert.ok(rt.load('on(start) :- oops(').error, 'a syntax error is reported');
});

// what a learner does in each tute step, and the check it must pass
const SOLVE = {
  menus: [(rt) => choose(rt, 'bar', ['Colour', 'Red']), (rt) => choose(rt, 'bar', ['Colour', 'Cool', 'Green']), (rt) => choose(rt, 'bar', ['Brush', 'Big'])],
  popups: [(rt) => choose(rt, 'context', ['Purple']), (rt) => choose(rt, 'context', ['Brush', 'Size', 'Thick']), (rt) => { ev(rt, 'key(m)'); assert.equal(rt.requests.pop().popup, 'sizes'); choose(rt, 'sizes', ['Size', '40 pixels']); }],
  events: [(rt) => ev(rt, 'down(100, 100)'), (rt) => { ev(rt, 'down(20, 50)'); ev(rt, 'drag(500, 300)'); ev(rt, 'up(500, 300)'); }, (rt) => ev(rt, 'key(x)')],
  painting: [(rt) => { ev(rt, 'key(q)'); ev(rt, 'down(100, 100)'); ev(rt, 'drag(300, 200)'); ev(rt, 'drag(450, 100)'); }, (rt) => { ev(rt, 'key(f)'); ev(rt, 'down(2, 2)'); }, (rt) => { ev(rt, 'down(100, 100)'); ev(rt, 'drag(200, 100)'); ev(rt, 'up(200, 100)'); ev(rt, 'key(u)'); }],
  shapes: [(rt) => ['down(50, 250)', 'down(150, 250)', 'down(250, 250)'].forEach((e) => ev(rt, e)), (rt) => ev(rt, 'down(100, 100)'), (rt) => { ev(rt, 'down(80, 150)'); ev(rt, 'drag(400, 150)'); ev(rt, 'up(400, 150)'); }],
  groups: [(rt) => { ev(rt, 'down(100, 200)'); ev(rt, 'drag(400, 200)'); ev(rt, 'up(400, 200)'); }, (rt) => ev(rt, 'down(130, 130)'), (rt) => ev(rt, 'key(u)')],
  layers: [(rt) => ['down(100, 100)', 'down(200, 100)', 'down(300, 100)'].forEach((e) => ev(rt, e)), (rt) => rt.run('show_layer(front, false)'), (rt) => { ev(rt, 'down(300, 190)'); ev(rt, 'key(m)'); }],
  editor: [(rt) => { ev(rt, 'down(100, 150)'); ev(rt, 'drag(400, 150)'); ev(rt, 'up(400, 150)'); }, (rt) => { ev(rt, 'down(10, 10)'); ev(rt, 'drag(590, 350)'); ev(rt, 'up(590, 350)'); }, (rt) => { ev(rt, 'down(200, 160)'); ev(rt, 'drag(330, 200)'); ev(rt, 'up(330, 200)'); }],
  dragdrop: [(rt) => { ev(rt, 'drop(ball, 100, 100)'); ev(rt, 'drop(ball, 200, 100)'); }, (rt) => ev(rt, 'drop(paint(red), 100, 150)'), (rt) => { ev(rt, 'down(120, 120)'); ev(rt, 'drag(500, 260)'); ev(rt, 'up(500, 260)'); }],
  pointers: [(rt) => ev(rt, "key('4')"), (rt) => [1, 2, 3, 4, 5].forEach(() => ev(rt, 'key(up)')), (rt) => ev(rt, 'key(s)')],
  state: [(rt) => ['down(10, 10)', 'down(20, 10)', 'down(30, 10)'].forEach((e) => ev(rt, e)), (rt) => { ev(rt, 'down(100, 100)'); ev(rt, 'down(400, 100)'); }, (rt) => rt.run('add(circle)')]
};

test('every tute step loads, its check waits for the learner, and doing the step passes it', () => {
  for (const t of TUTES) {
    const tute = parseTute(P, file(`tutes/${t.id}.pl`));
    assert.equal(tute.steps.length, t.steps, t.id);
    tute.steps.forEach((s, i) => {
      const rt = new Runtime(P);
      const loaded = rt.load(s.code);
      assert.equal(loaded.error, null, `${t.id} ${s.n}`);
      assert.equal(rt.holds(s.check), false, `${t.id} ${s.n}: passes before anything is done`);
      SOLVE[t.id][i](rt);
      assert.equal(rt.holds(s.check), true, `${t.id} ${s.n}: still not passed (${s.hint})`);
    });
  }
});
