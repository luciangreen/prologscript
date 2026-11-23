// PrologScript: the app. A program runs on the left; its code is on the right, with the clause
// that just ran marked, and a trace of each event and the commands it gave.
import { engine } from './lib/engine.js';
import { Runtime } from './lib/runtime.js';
import { View } from './lib/view.js';
import { TUTES, loadTute } from './lib/tutes.js';

const $ = (id) => document.getElementById(id);
const h = (tag, props = {}, ...kids) => { const e = Object.assign(document.createElement(tag), props); for (const k of kids.flat()) if (k !== null && k !== undefined && k !== false) e.append(k); return e; };
const store = {
  get(k, d) { try { return JSON.parse(localStorage.getItem(`prologscript.${k}`)) ?? d; } catch { return d; } },
  set(k, v) { try { localStorage.setItem(`prologscript.${k}`, JSON.stringify(v)); } catch { /* private browsing */ } }
};

const STARTER = `% My program: change it and press Run.
title("My program").
canvas(700, 420, white).

menu_bar([menu("Colour", [item("Red", brush(colour, red)), item("Blue", brush(colour, blue))])]).

on(start) :- say("Draw with the mouse or a finger.").
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
`;

let P, now = null; // now: { rt, view, name, original, kind }
const code = $('codeText');

// ---- running a program
async function run(source, { name, original = source, kind = 'program', after } = {}) {
  now?.view?.destroy();
  $('stage').replaceChildren();
  code.value = source;
  drawGutter();
  $('codeName').textContent = name ?? '';
  $('trace').replaceChildren();
  const rt = new Runtime(P);
  const loaded = rt.load(source);
  now = { rt, name, original, kind, after };
  if (!loaded.ok && loaded.error && !rt.clauses) {
    $('stage').replaceChildren(h('p', { className: 'err', textContent: `The program didn't load: ${loaded.error}` }));
    return now;
  }
  now.view = new View($('stage'), rt, { ran: (r) => ran(r), save: saveFile });
  if (loaded.start) ran(loaded.start);
  if (loaded.error) msg(`It loaded, but on(start) went wrong: ${loaded.error}`, true); else msg('');
  return now;
}

function ran(r) {
  traceAdd(r);
  if (!/^on\((drag|hover)\(/.test(r.goal)) mark(now.rt.clausesFor(r.goal));
  now.after?.(r);
}

// ---- the code, with the clause that ran marked
function drawGutter() {
  const n = code.value.split('\n').length;
  $('gutter').textContent = Array.from({ length: n }, (_, i) => i + 1).join('\n');
  syncScroll();
}
function syncScroll() {
  $('gutter').scrollTop = code.scrollTop;
  $('ran').style.transform = `translateY(${6 - code.scrollTop}px)`;
}
function mark(clauses) {
  const LINE = 18;
  $('ran').replaceChildren(...clauses.map((c) => h('div', { style: `top:${(c.from - 1) * LINE}px;height:${(c.to - c.from + 1) * LINE}px` })));
  const c = clauses[0];
  if (c && !document.activeElement?.isSameNode(code)) {
    const top = (c.from - 1) * LINE, bottom = c.to * LINE;
    if (top < code.scrollTop || bottom > code.scrollTop + code.clientHeight) code.scrollTop = Math.max(0, top - 2 * LINE);
    syncScroll();
  }
}
code.addEventListener('scroll', syncScroll);
code.addEventListener('input', () => { drawGutter(); $('ran').replaceChildren(); });
code.addEventListener('keydown', (e) => {
  if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); $('runCode').click(); }
  if (e.key === 'Tab') { e.preventDefault(); const { selectionStart: a, selectionEnd: b } = code; code.setRangeText('    ', a, b, 'end'); drawGutter(); }
});
$('runCode').addEventListener('click', async () => {
  const src = code.value;
  if (now.kind === 'mine') store.set('mine', src);
  const keep = { name: now.name, original: now.original, kind: now.kind, after: now.after };
  await run(src, keep);
  msg('Ran your code.');
});
$('resetCode').addEventListener('click', () => run(now.original, { name: now.name, original: now.original, kind: now.kind, after: now.after }));
$('downloadCode').addEventListener('click', () => saveFile(`${(now.name || 'program').replace(/\W+/g, '_')}.pl`, code.value, 'text/plain'));
$('sideToggle').addEventListener('click', () => {
  const closed = !$('side').classList.toggle('closed');
  $('main').classList.toggle('side-closed', !closed);
  $('sideToggle').setAttribute('aria-expanded', String(closed));
  store.set('sideClosed', !closed);
  now?.view?.resize();
});
if (store.get('sideClosed', false)) $('sideToggle').click();
const msg = (t, bad) => { $('codeMsg').textContent = t; $('codeMsg').style.color = bad ? 'var(--bad)' : ''; };

// ---- the trace: each event, the commands it gave, and how it ended (drags are run together)
function traceAdd(r) {
  const list = $('trace');
  const kind = /^on\((\w+)/.exec(r.goal)?.[1];
  const first = list.firstElementChild;
  if (kind && (kind === 'drag' || kind === 'hover') && first?.dataset.kind === kind) {
    first.dataset.n = String(Number(first.dataset.n) + 1);
    first.querySelector('.goal').textContent = `?- ${r.goal}.   × ${first.dataset.n}`;
    first.querySelector('.cmds').replaceChildren(...cmdLines(r));
    return;
  }
  const li = h('li', {}, h('span', { className: 'goal', textContent: `?- ${r.goal}.` }), h('span', { className: 'cmds' }, ...cmdLines(r)));
  li.dataset.kind = kind ?? 'menu';
  li.dataset.n = '1';
  list.prepend(li);
  while (list.children.length > 60) list.lastChild.remove();
}
function cmdLines(r) {
  const out = r.commands.slice(0, 8).map((c) => h('span', { className: 'cmd', textContent: c }));
  if (r.commands.length > 8) out.push(h('span', { className: 'no', textContent: `… and ${r.commands.length - 8} more` }));
  if (r.error) out.push(h('span', { className: 'err', textContent: `✗ ${r.error}` }));
  else if (r.goal.startsWith('on(') && !r.handled && !r.commands.length) out.push(h('span', { className: 'no', textContent: 'no on/1 clause for this' }));
  return out;
}
$('clearTrace').addEventListener('click', () => $('trace').replaceChildren());

// ---- saving: a download (in LucianOS too, where it lands in Downloads)
function saveFile(name, data, type) {
  const blob = data instanceof Blob ? data : new Blob([data], { type });
  const a = h('a', { href: URL.createObjectURL(blob), download: name });
  document.body.append(a);
  a.click();
  setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  msg(`Saved ${name}.`);
}

// ---- the tutes: one for each element, each step a program to run, change and check
function tuteList() {
  now?.view?.destroy();
  now = null;
  $('lesson').hidden = false;
  const done = store.get('tutes', {});
  $('lesson').replaceChildren(
    h('h2', { textContent: 'Tutes: one for each part of PrologScript' }),
    h('p', { textContent: 'Each tute is a PrologScript file. A step shows a program: run it, try it, change it, then press Check.' }),
    h('div', { className: 'tute-list' }, ...TUTES.map((t, i) => h('a', { href: `#tute/${t.id}/1`, className: (done[t.id] ?? 0) >= t.steps ? 'done' : '' },
      h('strong', { textContent: `${i + 1}. ${t.title}` }), h('span', { className: 'quiet', textContent: t.about })))));
  $('stage').replaceChildren(h('p', { className: 'quiet', textContent: 'Choose a tute.' }));
  code.value = ''; drawGutter(); $('trace').replaceChildren(); $('codeName').textContent = '';
}
async function tute(id, n) {
  const t = await loadTute(P, id);
  const step = t.steps[n - 1] ?? t.steps[0];
  n = step.n;
  const lesson = $('lesson');
  lesson.hidden = false;
  const result = h('span', { className: 'check', role: 'status' });
  const check = () => {
    const ok = now?.rt?.holds(step.check);
    result.className = `check ${ok ? 'ok' : 'no'}`;
    result.textContent = ok ? '✓ Done!' : `Not yet: ${step.hint}`;
    if (ok) { const d = store.get('tutes', {}); d[id] = Math.max(d[id] ?? 0, n); store.set('tutes', d); }
    return ok;
  };
  lesson.replaceChildren(
    h('div', { className: 'step-of', textContent: `Tute: ${t.title} · step ${n} of ${t.steps.length}` }),
    h('h2', { textContent: step.title }),
    ...step.says.split(/\n\n+/).map((p) => h('p', {}, ...inline(p))),
    h('p', { className: 'quiet' }, h('strong', { textContent: 'Try it: ' }), ...inline(step.hint)),
    h('div', { className: 'nav' },
      h('button', { type: 'button', textContent: '← Back', disabled: n === 1, onclick: () => { location.hash = `#tute/${id}/${n - 1}`; } }),
      h('button', { type: 'button', textContent: 'Check', onclick: check }),
      h('button', { type: 'button', textContent: n === t.steps.length ? 'All tutes' : 'Next →', onclick: () => { location.hash = n === t.steps.length ? '#tutes' : `#tute/${id}/${n + 1}`; } }),
      result));
  // the check runs after every event too, so the tick comes as soon as it's done
  await run(step.code, { name: `${t.title}, step ${n}`, kind: 'tute', after: () => { if (!result.classList.contains('ok') && now?.rt?.holds(step.check)) check(); } });
}
// `code` in a lesson's text
const inline = (t) => t.split(/(`[^`]+`)/).map((s) => (s.startsWith('`') ? h('code', { textContent: s.slice(1, -1) }) : s));

// ---- where we are
async function route() {
  const [what, id, n] = (location.hash.slice(1) || 'paint').split('/');
  for (const a of document.querySelectorAll('.tabs a')) a.classList.toggle('on', a.dataset.go === (what === 'tute' ? 'tutes' : what));
  $('lesson').hidden = true;
  try {
    if (what === 'paint' || what === 'draw') {
      const src = await (await fetch(`demos/${what}.pl`)).text();
      await run(src, { name: `demos/${what}.pl`, kind: 'demo' });
    } else if (what === 'tutes') tuteList();
    else if (what === 'tute') await tute(id, Number(n) || 1);
    else if (what === 'mine') await run(store.get('mine', STARTER), { name: 'my program', original: STARTER, kind: 'mine' });
  } catch (e) {
    $('stage').replaceChildren(h('p', { className: 'err', textContent: e.message }));
  }
}

P = await engine();
addEventListener('hashchange', route);
route();
