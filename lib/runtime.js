// The runtime: a prologscript program running on the pl2detlog interpreter. Prolog calls the
// commands below; each one changes the picture, the scene or the menus at once (so a query later
// in the same goal sees the change). Nothing here touches the page: lib/view.js draws the state.
//
// The commands, as Prolog sees them (see README.md for the whole list):
//   painting   paint(dot(X,Y)) paint(line(X1,Y1,X2,Y2)) paint(fill(X,Y)) paint(spray(X,Y)) paint(clear)
//              brush(colour|size|tip, Value) (unbound Value reads it), brush_is(Key, Value) (tests it),
//              colour_at(X, Y, C), painted(Count), undo
//   shapes     shape(Id, Shape) shape(Id, Shape, Style) restyle(Id, Style) reshape(Id, Shape)
//              move(Id, DX, DY) resize(Id, [X,Y,W,H]) delete(Id) group(Ids, G) ungroup(G)
//              raise(Id) lower(Id) front(Id) back(Id) select(Ids) selection(Ids)
//              shape_at(X, Y, Id) part_at(X, Y, Id) bounds(Id, [X,Y,W,H]) shape_of(Id, Shape)
//              style_of(Id, [fill(F), stroke(S), width(W)]) shapes(Ids) new_id(Prefix, Id)
//   layers     new_layer(Id, Name) rename_layer(Id, Name) layer_name(Id, Name) use_layer(Id) active_layer(Id) layers(Ids) show_layer(Id, Bool)
//              lock_layer(Id, Bool) layer_shown(Id) layer_locked(Id) items_in(Layer, Ids) layer_up(Id) layer_down(Id) to_layer(Id, Layer) delete_layer(Id)
//   editor     edit(down(X,Y)) edit(drag(X,Y)) edit(up(X,Y)) (edit(add_down(X,Y)) adds to the selection)
//   on screen  popup(Name) pointer(Spec) say(Text) save_picture(Name) save_drawing(Name)
//              held(shift|alt|meta|control) pointer_at(X, Y) pointer_now(Spec)
// A program declares: title/1, canvas/3, menu_bar/1, popup_menu/2, pointer_shape/2, palette/1,
// panel/1, and handles events with on/1: start, down(X,Y), drag(X,Y), up(X,Y), right(X,Y),
// key(K), drop(Thing, X, Y), hover(X,Y).

import * as S from './scene.js';
import * as Pt from './paint.js';
import { cursor } from './pointer.js';
import * as Ed from './editor.js';

let current = null; // the runtime whose goal is running (the interpreter's built-ins are shared)
const installed = new WeakSet();
export const UNDO_DEPTH = 15;

export class Runtime {
  constructor(P) {
    this.P = P;
    install(P);
    this.reset();
  }

  reset() {
    this.scene = S.empty();
    this.canvasSize = [800, 500];
    this.background = 0xffffff;
    this.bitmap = Pt.bitmap(800, 500, this.background);
    this.brush = { colour: 0x222222, size: 6, tip: 'round' };
    this.pointerSpec = 'crosshair';
    this.pointerCss = 'crosshair';
    this.pointerText = 'crosshair';
    this.status = '';
    this.requests = [];
    this.undoStack = [];
    this.snap = null;
    this.editor = Ed.idle();
    this.dirty = { paint: 'all', scene: true };
    this.version = 0;
    this.at = [0, 0];
    this.held = new Set();
    this.decl = { title: 'PrologScript', menuBar: [], popups: [], pointers: new Map(), palette: [], panels: [] };
    this.log = [];
    this.lastError = null;
    this.spraySeed = 1;
  }

  // ---- loading
  load(source) {
    const P = this.P;
    this.reset();
    this.source = source;
    // no compiled accelerators: events run on the Prolog route anyway, and LucianOS's security policy
    // doesn't allow code made at run time
    this.it = new P.Interpreter({ stepLimit: 2e6, timeLimitMs: 4000, noAccel: true });
    this.it.setProgram(`${source}\n${PRELUDE}`);
    if (this.it.loadError) return { ok: false, error: this.it.loadError };
    this.clauses = splitClauses(P, source);
    this.handles = new Set(this.clauses.filter((c) => c.on).map((c) => c.on)); // events the program has clauses for
    const r = this.query('ps_declarations');
    if (r.error) return { ok: false, error: r.error };
    for (const t of r.notes) {
      if (t.f === 'title') this.decl.title = String(t.a[0]);
      else if (t.f === 'canvas') {
        const [w, h, bg] = t.a;
        this.canvasSize = [Math.round(w), Math.round(h)];
        this.background = Pt.colour(bg ?? 'white');
        this.bitmap = Pt.bitmap(this.canvasSize[0], this.canvasSize[1], this.background);
      } else if (t.f === 'popup_menu') this.decl.popups.push(String(t.a[0]));
      else if (t.f === 'pointer_shape') this.decl.pointers.set(String(t.a[0]), t.a[1]);
      else if (t.f === 'palette') this.decl.palette = (t.a[0] || []).map(tile);
      else if (t.f === 'panel') this.decl.panels.push(String(t.a[0]));
    }
    this.dirty = { paint: 'all', scene: true };
    const start = this.event('start');
    this.undoStack = [];
    return { ok: !start.error, error: start.error, start };
  }

  // run a goal; the host commands it calls are logged, and ps_note/1 terms collected
  query(goalText, { log = false } = {}) {
    const prev = current;
    current = this;
    this.notes = [];
    this.lastError = null;
    const before = this.log.length;
    const t0 = performance.now();
    let r;
    try { r = this.it.run(goalText); } catch (e) { r = { error: e.message, answers: [] }; } finally { current = prev; }
    const error = this.lastError ?? (r.error ? errorText(r.error) : null);
    const out = { ok: !error && r.answers?.length > 0, error, output: r.output || '', notes: this.notes, ms: performance.now() - t0, commands: this.log.slice(before) };
    if (!log) this.log.length = before;
    return out;
  }

  // an event: on(Event), with the undo point it opens or closes. Event: a Prolog term's text.
  event(ev, { x, y } = {}) {
    if (x !== undefined) this.at = [x, y];
    const kind = /^[a-z_]+/.exec(ev)?.[0] ?? ev;
    if (kind === 'hover' && !this.handles.has('hover')) return { skipped: true };
    const opens = ['down', 'right', 'drop', 'key', 'start'].includes(kind);
    if (opens) this.openSnap();
    const r = this.query(`ps_event(${ev})`, { log: true });
    r.goal = `on(${ev})`;
    r.handled = r.notes.some((n) => n === 'handled');
    if (kind === 'right' && !r.handled && this.decl.popups.includes('context')) { this.requests.push({ popup: 'context', at: this.at }); r.handled = true; r.commands.push('popup(context)   % no on(right(..)) clause, so the pop-up menu called context'); }
    if (kind !== 'down' && kind !== 'drag') this.closeSnap();
    this.log = this.log.slice(-400);
    return r;
  }
  // a menu item's goal
  run(goalText) {
    this.openSnap();
    const r = this.query(`ps_menu_goal((${goalText}))`, { log: true });
    r.goal = goalText;
    this.closeSnap();
    return r;
  }
  // does a goal succeed? (a menu's checked/enabled conditions, a tute's checks)
  holds(goalText) {
    const r = this.query(`ps_holds((${goalText}))`);
    return r.notes.includes('yes');
  }
  // a menu, read from the program when it opens: menu_bar or popup_menu(Name)
  menu(which) {
    const r = this.query(which === 'bar' ? 'ps_menu_bar' : `ps_popup(${quoteAtom(which)})`);
    if (r.error) throw new Error(r.error);
    const t = r.notes[0];
    return t ? this.menuItems(t) : [];
  }
  menuItems(list) {
    const out = [];
    for (const e of Array.isArray(list) ? list : []) {
      if (typeof e === 'string' || e instanceof String) { if (String(e) === 'separator' || String(e) === '-') out.push({ type: 'sep' }); continue; }
      if (e?.f === 'item' && e.a.length >= 2) {
        const opts = e.a[2] ?? [];
        const it = { type: 'item', label: String(e.a[0]), goal: e.a[1].text ?? String(e.a[1]) };
        for (const o of Array.isArray(opts) ? opts : []) {
          if (o?.f === 'key') it.key = String(o.a[0]);
          if (o?.f === 'checked') it.checked = this.holds(o.a[0].text);
          if (o?.f === 'enabled') it.enabled = this.holds(o.a[0].text);
        }
        out.push(it);
      } else if (e?.f === 'menu' && e.a.length === 2) {
        let items = e.a[1];
        if (items?.f === 'from') {
          const q = this.query(`ps_from((${items.a[0].text}))`);
          items = q.notes[0] ?? [];
        }
        out.push({ type: 'menu', label: String(e.a[0]), items: this.menuItems(items) });
      }
    }
    return out;
  }

  // ---- undo points: one per press (down .. up), menu choice, key, drop
  openSnap() { this.closeSnap(); this.snap = { scene: this.scene, bitmap: null, version: this.version }; }
  closeSnap() {
    if (!this.snap) return;
    if (this.version !== this.snap.version) { this.undoStack.push(this.snap); if (this.undoStack.length > UNDO_DEPTH) this.undoStack.shift(); }
    this.snap = null;
  }
  changed(paintBox) {
    this.version++;
    if (paintBox !== undefined) {
      if (paintBox === 'all' || this.dirty.paint === 'all') this.dirty.paint = 'all';
      else if (paintBox) this.dirty.paint = this.dirty.paint ? [Math.min(this.dirty.paint[0], paintBox[0]), Math.min(this.dirty.paint[1], paintBox[1]), Math.max(this.dirty.paint[2], paintBox[2]), Math.max(this.dirty.paint[3], paintBox[3])] : paintBox;
    } else this.dirty.scene = true;
  }
  beforePaint() { if (this.snap && !this.snap.bitmap) this.snap.bitmap = Pt.copyOf(this.bitmap); }
  undo() {
    if (this.snap && this.version !== this.snap.version) this.closeSnap();
    const u = this.undoStack.pop();
    if (!u) return false;
    this.scene = u.scene;
    if (u.bitmap) { this.bitmap = u.bitmap; this.dirty.paint = 'all'; }
    this.dirty.scene = true;
    this.version++;
    return true;
  }

  // which clauses would answer a goal (for showing the code that ran): [{ from, to }] lines
  clausesFor(goalText) {
    const P = this.P;
    let g;
    try { g = P.deref(P.readTerm(goalText).term); } catch { return []; }
    const key = P.key(g);
    return this.clauses.filter((c) => c.key === key && this.unifies(c.head, goalText)).slice(0, 1);
  }
  unifies(head, goalText) {
    const r = this.query(`ps_holds(\\+ \\+ (${head} = ${goalText}))`);
    return r.notes.includes('yes');
  }
}

// the Prolog side: declarations, events and conditions, through ps_note/1
const PRELUDE = `
ps_declarations :-
  forall(catch(title(T), _, fail), ps_note(title(T))),
  forall(catch(canvas(W, H, B), _, fail), ps_note(canvas(W, H, B))),
  forall(catch(canvas(W, H), _, fail), ps_note(canvas(W, H, white))),
  forall(catch(popup_menu(N, _), _, fail), ps_note(popup_menu(N))),
  forall(catch(pointer_shape(N, S), _, fail), ps_note(pointer_shape(N, S))),
  forall(catch(palette(P), _, fail), ps_note(palette(P))),
  forall(catch(panel(P), _, fail), ps_note(panel(P))).
ps_event(E) :- ( catch(on(E), Err, (ps_unless_missing(Err), fail)) -> ps_note(handled) ; true ).
ps_unless_missing(error(existence_error(procedure, on/1), _)) :- !.
ps_unless_missing(Err) :- ps_caught(Err).
ps_menu_goal(G) :- ( catch(G, Err, (ps_caught(Err), fail)) -> true ; true ).
ps_holds(G) :- ( catch(G, _, fail) -> ps_note(yes) ; ps_note(no) ).
ps_menu_bar :- ( catch(menu_bar(M), _, fail) -> ps_note_menu(M) ; true ).
ps_popup(N) :- ( catch(popup_menu(N, M), _, fail) -> ps_note_menu(M) ; true ).
ps_from(G) :- ( catch(call(G, Items), _, fail) -> ps_note_menu(Items) ; ps_note([]) ).
`;

const quoteAtom = (s) => (/^[a-z][A-Za-z0-9_]*$/.test(s) ? s : `'${String(s).replace(/\\/g, '\\\\').replace(/'/g, "\\'")}'`);
const errorText = (e) => String(e).replace(/^error\((.*),\s*_\w*\)$/, '$1').replace(/^prologscript\("(.*)"\)$/, '$1');
const tile = (t) => (t?.f === 'tile' ? { label: String(t.a[0]), thing: t.a[1].text ?? String(t.a[1]), icon: t.a[2] !== undefined ? String(t.a[2]) : '' } : { label: String(t), thing: String(t), icon: '' });

// the source's clauses, with their lines, heads and predicate keys
export function splitClauses(P, src) {
  const out = [];
  let rest = src, offset = 0;
  for (;;) {
    const t = P.nextClauseText(rest);
    if (t === null) break;
    const lead = skipLayout(t);
    const startAt = offset + lead, endAt = offset + t.length;
    const text = src.slice(startAt, endAt);
    const line = (i) => src.slice(0, i).split('\n').length;
    let head = null, key = null, on = null;
    try {
      const term = P.deref(P.readTerm(text).term);
      const h = term.t === 'c' && term.f === ':-' && term.a.length === 2 ? P.deref(term.a[0]) : term;
      if (!(term.t === 'c' && term.f === ':-' && term.a.length === 1)) {
        head = P.show(h, { quoted: true });
        key = P.key(h);
        if (key === 'on/1') on = P.name(h.a[0]);
      }
    } catch { /* a syntax error shows when it loads */ }
    out.push({ from: line(startAt), to: line(endAt - 1), head, key, on });
    rest = rest.slice(t.length);
    offset += t.length;
  }
  return out;
}

// how much of a clause's text is layout and comments before it
function skipLayout(t) {
  let i = 0;
  for (;;) {
    while (i < t.length && /\s/.test(t[i])) i++;
    if (t[i] === '%') { while (i < t.length && t[i] !== '\n') i++; continue; }
    if (t[i] === '/' && t[i + 1] === '*') { const j = t.indexOf('*/', i + 2); i = j < 0 ? t.length : j + 2; continue; }
    return i;
  }
}

// ---- Prolog terms and JavaScript values
function toJS(P, t) {
  t = P.deref(t);
  switch (t.t) {
    case 'n': return Number(t.v);
    case 's': return t.v;
    case 'a': return t.n === '[]' ? [] : t.n;
    case 'v': return undefined;
    case 'c': {
      const arr = P.listToArray(t);
      if (arr) return arr.map((x) => toJS(P, x));
      const o = { f: t.f, a: t.a.map((x) => toJS(P, x)) };
      // a term's own text too, for goals carried as data (menu items, palette things)
      Object.defineProperty(o, 'text', { value: P.show(t, { quoted: true }), enumerable: false });
      return o;
    }
    default: return undefined;
  }
}
function fromJS(P, v) {
  if (typeof v === 'number') return Number.isInteger(v) ? P.Int(v) : P.Num(v, true);
  if (typeof v === 'boolean') return P.Atom(String(v));
  if (Array.isArray(v)) return P.list(v.map((x) => fromJS(P, x)));
  if (v && v.atom !== undefined) return P.Atom(v.atom);
  if (v && v.f) return P.Cmp(v.f, v.a.map((x) => fromJS(P, x)));
  return P.Str(String(v));
}
const atom = (s) => ({ atom: s });
const term = (f, ...a) => ({ f, a });

// a shape term -> { kind, g }
function shapeOf(v) {
  const pts = (l) => {
    if (!Array.isArray(l)) throw new Error('points: a list such as [10-20, 30-40]');
    return l.map((p) => (Array.isArray(p) ? p : p?.f === '-' ? p.a : null) ?? (() => { throw new Error('a point is X-Y'); })());
  };
  const a = v?.a ?? [];
  switch (v?.f) {
    case 'rect': return { kind: 'rect', g: a };
    case 'square': return { kind: 'rect', g: [a[0], a[1], a[2], a[2]] };
    case 'ellipse': return { kind: 'ellipse', g: a };
    case 'circle': return { kind: 'ellipse', g: [a[0], a[1], a[2], a[2]] };
    case 'line': return { kind: 'line', g: a };
    case 'polygon': case 'poly': return { kind: 'poly', g: pts(a[0]) };
    case 'path': return { kind: 'path', g: pts(a[0]) };
    case 'text': return a.length === 3 ? { kind: 'text', g: [a[0], a[1], 20, String(a[2])] } : { kind: 'text', g: [a[0], a[1], a[2], String(a[3])] };
    default: throw new Error(`${v?.f ?? v} isn't a shape (rect, square, ellipse, circle, line, polygon, path, text)`);
  }
}
function shapeTerm(n) {
  const g = n.g, P2 = (l) => l.map(([x, y]) => term('-', x, y));
  switch (n.kind) {
    case 'rect': return term('rect', ...g);
    case 'ellipse': return term('ellipse', ...g);
    case 'line': return term('line', ...g);
    case 'poly': return term('polygon', P2(g));
    case 'path': return term('path', P2(g));
    case 'text': return term('text', g[0], g[1], g[2], g[3]);
    case 'group': return term('group', n.items.map(atom));
    default: return atom(n.kind);
  }
}
function styleOf(v) {
  const st = {};
  for (const p of Array.isArray(v) ? v : [v]) {
    if (p?.f === 'fill' || p?.f === 'stroke') st[p.f] = p.a[0] === 'none' ? 'none' : Pt.hex(Pt.colour(p.a[0]));
    else if (p?.f === 'width') st.width = p.a[0];
    else throw new Error(`${p?.f ?? p}: a style is fill(C), stroke(C) or width(W)`);
  }
  return st;
}
const idOf = (v) => { if (typeof v !== 'string') throw new Error('a name such as box1'); return v; };
const bool = (v) => { if (v !== 'true' && v !== 'false') throw new Error('true or false'); return v === 'true'; };

// ---- the commands
function install(P) {
  if (installed.has(P)) return;
  installed.add(P);
  const fail = (msg) => { throw new P.PlError(P.Cmp('error', [P.Cmp('prologscript', [P.Str(msg)]), P.Var()])); };
  // a command: checks and changes the running program's state; errors become Prolog errors
  const def = (name, arity, fn, { effect = true, logged = true } = {}) => {
    const k = `${name}/${arity}`;
    P.builtins[k] = {
      fn: (a, e) => {
        const rt = current;
        if (!rt) return false;
        const args = a.map((x) => toJS(P, x));
        const note = () => { if (logged) rt.log.push(P.show(P.Cmp(name, a.map((x) => P.deref(x))), { quoted: true })); };
        try {
          const out = fn(rt, args, a);
          if (out === false) return false;
          const ok = out && out.unify ? out.unify.every(([i, v]) => e.unify(a[i], fromJS(P, v))) : true;
          if (ok) note(); // shown as it ran, with what it answered
          return ok;
        } catch (err) {
          note();
          if (err instanceof P.PlError) throw err;
          rt.lastError = err.message;
          fail(err.message);
        }
      }
    };
    if (effect) P.interp.EFFECTS.add(k);
  };
  const isVar = (t) => P.deref(t).t === 'v';
  const scene = (rt, s) => { rt.scene = s; rt.changed(); };

  // bookkeeping
  def('ps_note', 1, (rt, [v]) => { rt.notes.push(v); }, { logged: false });
  def('ps_note_menu', 1, (rt, _, a) => { rt.notes.push(menuTerm(P, a[0])); }, { logged: false });
  def('ps_caught', 1, (rt, [v], a) => { rt.lastError = rt.lastError ?? errorText(P.show(P.deref(a[0]), { quoted: true })); }, { logged: false });

  // painting
  def('paint', 1, (rt, [s]) => {
    const st = typeof s === 'string' ? { op: s } : { op: s?.f };
    const a = s?.a ?? [];
    if (st.op === 'dot' || st.op === 'fill' || st.op === 'spray') [st.x, st.y] = a;
    else if (st.op === 'line') [st.x1, st.y1, st.x2, st.y2] = a;
    else if (st.op !== 'clear') throw new Error(`paint: dot(X,Y), line(X1,Y1,X2,Y2), fill(X,Y), spray(X,Y) or clear`);
    for (const k of ['x', 'y', 'x1', 'y1', 'x2', 'y2']) if (k in st && typeof st[k] !== 'number') throw new Error(`paint: ${k} is a number`);
    if (st.op === 'spray') st.seed = rt.spraySeed++;
    rt.beforePaint();
    const brush = st.op === 'clear' ? { ...rt.brush, colour: rt.background } : rt.brush;
    const box = Pt.apply(rt.bitmap, st, brush);
    if (box) rt.changed(st.op === 'clear' ? 'all' : box);
  });
  def('brush', 2, (rt, [k, v], a) => {
    if (!['colour', 'color', 'size', 'tip'].includes(k)) throw new Error('brush: colour, size or tip');
    const key = k === 'color' ? 'colour' : k;
    if (isVar(a[1])) return { unify: [[1, key === 'colour' ? Pt.hex(rt.brush.colour) : key === 'tip' ? atom(rt.brush.tip) : rt.brush.size]] };
    if (key === 'colour') rt.brush.colour = Pt.colour(v);
    if (key === 'size') { if (typeof v !== 'number' || v < 1 || v > 120) throw new Error('brush size: 1 to 120'); rt.brush.size = v; }
    if (key === 'tip') { if (v !== 'round' && v !== 'square') throw new Error('brush tip: round or square'); rt.brush.tip = v; }
  });
  def('brush_is', 2, (rt, [k, v]) => {
    if (k === 'colour' || k === 'color') return rt.brush.colour === Pt.colour(v);
    if (k === 'size') return rt.brush.size === v;
    if (k === 'tip') return rt.brush.tip === v;
    return false;
  }, { logged: false });
  def('colour_at', 3, (rt, [x, y]) => {
    const X = Math.round(x), Y = Math.round(y);
    if (X < 0 || Y < 0 || X >= rt.bitmap.w || Y >= rt.bitmap.h) return false;
    return { unify: [[2, Pt.hex(Pt.get(rt.bitmap, X, Y))]] };
  }, { logged: false });
  def('undo', 0, (rt) => rt.undo());
  def('painted', 1, (rt) => { let n = 0; const px = rt.bitmap.px, bg = rt.background; for (let i = 0; i < px.length; i++) if (px[i] !== bg) n++; return { unify: [[0, n]] }; }, { logged: false });
  def('canvas_size', 2, (rt) => ({ unify: [[0, rt.canvasSize[0]], [1, rt.canvasSize[1]]] }), { logged: false });

  // shapes
  def('shape', 2, (rt, [id, sh]) => { const { kind, g } = shapeOf(sh); scene(rt, S.add(rt.scene, idOf(id), kind, g, {})); });
  def('shape', 3, (rt, [id, sh, st]) => { const { kind, g } = shapeOf(sh); scene(rt, S.add(rt.scene, idOf(id), kind, g, styleOf(st))); });
  def('restyle', 2, (rt, [id, st]) => scene(rt, S.restyle(rt.scene, idOf(id), styleOf(st))));
  def('reshape', 2, (rt, [id, sh]) => { const { kind, g } = shapeOf(sh); scene(rt, S.reshape(rt.scene, idOf(id), kind, g)); });
  def('move', 3, (rt, [id, dx, dy]) => scene(rt, S.move(rt.scene, idOf(id), dx, dy)));
  def('resize', 2, (rt, [id, b]) => scene(rt, S.scaleTo(rt.scene, idOf(id), b)));
  def('delete', 1, (rt, [id]) => scene(rt, S.remove(rt.scene, idOf(id))));
  def('group', 2, (rt, [ids, g]) => scene(rt, S.group(rt.scene, ids, idOf(g))));
  def('ungroup', 1, (rt, [g]) => scene(rt, S.ungroup(rt.scene, idOf(g))));
  for (const how of ['raise', 'lower', 'front', 'back']) def(how, 1, (rt, [id]) => scene(rt, S.restack(rt.scene, idOf(id), how)));
  def('select', 1, (rt, [ids]) => { rt.scene = S.select(rt.scene, ids); rt.dirty.scene = true; });
  def('selection', 1, (rt) => ({ unify: [[0, rt.scene.selected.map(atom)]] }), { logged: false });
  def('shape_at', 3, (rt, [x, y]) => { const id = S.hit(rt.scene, x, y); return id ? { unify: [[2, atom(id)]] } : false; }, { logged: false });
  def('part_at', 3, (rt, [x, y]) => { const id = S.hit(rt.scene, x, y, true); return id ? { unify: [[2, atom(id)]] } : false; }, { logged: false });
  def('bounds', 2, (rt, [id]) => ({ unify: [[1, S.bounds(rt.scene, idOf(id))]] }), { logged: false });
  def('shape_of', 2, (rt, [id]) => { const n = rt.scene.nodes[idOf(id)]; if (!n) return false; return { unify: [[1, shapeTerm(n)]] }; }, { logged: false });
  def('style_of', 2, (rt, [id]) => { const n = rt.scene.nodes[idOf(id)]; if (!n || n.kind === 'group') return false; return { unify: [[1, [term('fill', n.style.fill), term('stroke', n.style.stroke), term('width', n.style.width)]]] }; }, { logged: false });
  def('shapes', 1, (rt) => ({ unify: [[0, rt.scene.layers.flatMap((l) => l.items).map(atom)]] }), { logged: false });
  def('new_id', 2, (rt, [p]) => ({ unify: [[1, atom(S.newId(rt.scene, p))]] }), { logged: false });

  // layers
  def('new_layer', 2, (rt, [id, name]) => scene(rt, S.addLayer(rt.scene, idOf(id), name)));
  def('use_layer', 1, (rt, [id]) => scene(rt, S.useLayer(rt.scene, idOf(id))));
  def('active_layer', 1, (rt) => ({ unify: [[0, atom(rt.scene.active)]] }), { logged: false });
  def('layers', 1, (rt) => ({ unify: [[0, rt.scene.layers.map((l) => atom(l.id))]] }), { logged: false });
  def('items_in', 2, (rt, [id]) => { const l = rt.scene.layers.find((x) => x.id === id); return l ? { unify: [[1, l.items.map(atom)]] } : false; }, { logged: false });
  def('layer_locked', 1, (rt, [id]) => !!rt.scene.layers.find((x) => x.id === id)?.locked, { logged: false });
  def('layer_shown', 1, (rt, [id]) => !!rt.scene.layers.find((x) => x.id === id)?.shown, { logged: false });
  def('rename_layer', 2, (rt, [id, name]) => scene(rt, S.renameLayer(rt.scene, idOf(id), name)));
  def('layer_name', 2, (rt, [id]) => { const l = rt.scene.layers.find((x) => x.id === id); return l ? { unify: [[1, l.name]] } : false; }, { logged: false });
  def('show_layer', 2, (rt, [id, b]) => scene(rt, S.setLayer(rt.scene, idOf(id), 'shown', bool(b))));
  def('lock_layer', 2, (rt, [id, b]) => scene(rt, S.setLayer(rt.scene, idOf(id), 'locked', bool(b))));
  def('layer_up', 1, (rt, [id]) => scene(rt, S.moveLayer(rt.scene, idOf(id), 'raise')));
  def('layer_down', 1, (rt, [id]) => scene(rt, S.moveLayer(rt.scene, idOf(id), 'lower')));
  def('to_layer', 2, (rt, [id, l]) => scene(rt, S.toLayer(rt.scene, idOf(id), idOf(l))));
  def('delete_layer', 1, (rt, [id]) => scene(rt, S.removeLayer(rt.scene, idOf(id))));

  // the editor
  def('edit', 1, (rt, [ev]) => {
    const type = ev?.f, add = type === 'add_down';
    if (!['down', 'drag', 'up', 'add_down'].includes(type)) throw new Error('edit: down(X,Y), drag(X,Y), up(X,Y) or add_down(X,Y)');
    const before = rt.scene;
    const r = Ed.edit(rt.editor, rt.scene, { type: add ? 'down' : type, at: ev.a, add });
    rt.editor = r.state;
    if (r.scene !== before) { const moved = r.scene.nodes !== before.nodes; rt.scene = r.scene; if (moved) rt.changed(); else rt.dirty.scene = true; }
    rt.dirty.scene = true;
  });

  // on screen
  def('popup', 1, (rt, [name]) => { if (!rt.decl.popups.includes(String(name))) throw new Error(`there is no popup_menu(${name}, ...)`); rt.requests.push({ popup: String(name), at: rt.at }); });
  def('pointer', 1, (rt, [spec], a) => {
    rt.pointerText = P.show(P.deref(a[0]), { quoted: true });
    const named = typeof spec === 'string' && rt.decl.pointers.has(spec) ? rt.decl.pointers.get(spec) : spec;
    rt.pointerCss = cursor(named).css;
    rt.pointerSpec = named;
    rt.dirty.pointer = true;
  });
  // the pointer as the program last set it (a name, or a description), read back as a term
  P.builtins['pointer_now/1'] = { fn: (a, e) => current && e.unify(a[0], P.readTerm(current.pointerText ?? 'crosshair').term) };
  def('held', 1, (rt, [k]) => rt.held.has(String(k)), { logged: false });
  def('pointer_at', 2, (rt) => ({ unify: [[0, rt.at[0]], [1, rt.at[1]]] }), { logged: false });
  def('say', 1, (rt, [t]) => { rt.status = String(Array.isArray(t) ? t.join('') : t).slice(0, 300); rt.dirty.status = true; });
  def('save_picture', 1, (rt, [n]) => { rt.requests.push({ save: 'picture', name: String(n) }); });
  def('save_drawing', 1, (rt, [n]) => { rt.requests.push({ save: 'drawing', name: String(n) }); });
}

// a menu term, read as data with each goal's own text
function menuTerm(P, t) {
  const conv = (x) => {
    x = P.deref(x);
    const arr = P.listToArray(x);
    if (arr) return arr.map(conv);
    if (x.t === 'c') {
      const o = { f: x.f, a: x.a.map(conv) };
      Object.defineProperty(o, 'text', { value: P.show(x, { quoted: true }), enumerable: false });
      return o;
    }
    if (x.t === 'a') return Object.assign(new String(x.n), { text: P.show(x, { quoted: true }) });
    return toJS(P, x);
  };
  return conv(t);
}
