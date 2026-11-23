// The view: draws a running program (menus, pop-ups, the painted canvas, the vector shapes, the
// editor's handles, the layers panel, the palette, the pointer and the status line) and turns
// what you do back into Prolog events. Works with a mouse, a pen or a finger.

import * as M from './menu.js';
import * as S from './scene.js';
import { element, svg as sceneSvg } from './svgout.js';
import { handles, HANDLE } from './editor.js';

const SVGNS = 'http://www.w3.org/2000/svg';
const h = (tag, props = {}, ...kids) => {
  const e = Object.assign(document.createElement(tag), props);
  for (const k of kids.flat()) if (k !== null && k !== undefined && k !== false) e.append(k);
  return e;
};
const s = (tag, attrs = {}) => { const e = document.createElementNS(SVGNS, tag); for (const [k, v] of Object.entries(attrs)) if (k !== '_text') e.setAttribute(k, v); if (attrs._text !== undefined) e.textContent = attrs._text; return e; };
const KEYS = { Delete: 'delete', Backspace: 'backspace', Escape: 'escape', Enter: 'enter', ArrowUp: 'up', ArrowDown: 'down', ArrowLeft: 'left', ArrowRight: 'right', ' ': 'space', Tab: 'tab' };
const atomText = (k) => (/^[a-z][a-z0-9_]*$/.test(k) ? k : `'${k.replace(/\\/g, '\\\\').replace(/'/g, "\\'")}'`);
const LONG_PRESS = 550;
// menus are placed in the window, so a cascade can use the room beside the program
const viewport = () => ({ left: 0, top: 0, width: innerWidth, height: innerHeight, right: innerWidth, bottom: innerHeight });

export class View {
  // rt: a Runtime with a program loaded. hooks: { ran(result), save(name, data, type) }
  constructor(root, rt, hooks = {}) {
    this.root = root;
    this.rt = rt;
    this.hooks = hooks;
    this.open = null; // { menu, path, at, from: 'bar' | 'popup', bar?: index }
    this.build();
    this.render();
  }

  build() {
    const rt = this.rt;
    const [w, hgt] = rt.canvasSize;
    this.menubar = h('div', { className: 'ps-menubar', role: 'menubar' });
    this.paintCanvas = h('canvas', { className: 'ps-paint', width: w, height: hgt });
    this.ctx = this.paintCanvas.getContext('2d');
    this.image = this.ctx.createImageData(w, hgt);
    this.rgba = new Uint32Array(this.image.data.buffer);
    this.vector = s('svg', { class: 'ps-vector', width: w, height: hgt, viewBox: `0 0 ${w} ${hgt}` });
    this.overlay = s('svg', { class: 'ps-overlay', width: w, height: hgt, viewBox: `0 0 ${w} ${hgt}` });
    this.stage = h('div', { className: 'ps-stage', tabIndex: 0, ariaLabel: 'Canvas' }, this.paintCanvas, this.vector, this.overlay);
    Object.assign(this.stage.style, { width: `${w}px`, height: `${hgt}px` });
    this.fit = h('div', { className: 'ps-fit' }, this.stage);
    this.palette = h('div', { className: 'ps-palette' });
    this.panel = h('div', { className: 'ps-panel' });
    this.status = h('div', { className: 'ps-status', ariaLive: 'polite' });
    this.menus = h('div', { className: 'ps-menus' });
    this.app = h('div', { className: 'ps-app', tabIndex: -1 },
      this.menubar,
      h('div', { className: 'ps-body' }, rt.decl.palette.length ? this.palette : null, this.fit, rt.decl.panels.includes('layers') ? this.panel : null),
      this.status, this.menus);
    this.root.replaceChildren(this.app);
    this.renderBar();
    this.renderPalette();
    this.wire();
    this.resize();
    this.ro = new ResizeObserver(() => this.resize());
    this.ro.observe(this.fit);
  }

  // the stage keeps its size in canvas units and is scaled to fit (an iPhone shows it whole)
  resize() {
    const [w, hgt] = this.rt.canvasSize;
    const avail = this.fit.clientWidth || w;
    this.scale = Math.min(1, (avail - 2) / w);
    this.stage.style.transform = `scale(${this.scale})`;
    this.fit.style.height = `${Math.ceil(hgt * this.scale) + 2}px`;
  }
  point(e) {
    const r = this.stage.getBoundingClientRect();
    return [Math.round((e.clientX - r.left) / this.scale), Math.round((e.clientY - r.top) / this.scale)];
  }

  // ---- events
  wire() {
    const st = this.stage;
    let pressed = null, pending = null, timer = null;
    const flush = () => { pending = null; };
    st.addEventListener('pointerdown', (e) => {
      if (e.button === 2) return;
      this.closeMenus();
      st.focus({ preventScroll: true });
      st.setPointerCapture(e.pointerId);
      const [x, y] = this.point(e);
      pressed = { id: e.pointerId, from: [x, y], moved: false };
      this.rt.held = new Set([e.shiftKey && 'shift', e.altKey && 'alt', e.metaKey && 'meta', e.ctrlKey && 'control'].filter(Boolean));
      this.send(`down(${x}, ${y})`, x, y);
      if (e.pointerType !== 'mouse') timer = setTimeout(() => { // a long press is a right click
        if (!pressed || pressed.moved) return;
        if (this.rt.snap && this.rt.version !== this.rt.snap.version) this.rt.undo();
        pressed = null;
        this.send(`right(${x}, ${y})`, x, y);
      }, LONG_PRESS);
      e.preventDefault();
    });
    st.addEventListener('pointermove', (e) => {
      const [x, y] = this.point(e);
      if (pressed && e.pointerId === pressed.id) {
        if (Math.abs(x - pressed.from[0]) + Math.abs(y - pressed.from[1]) > 6) pressed.moved = true;
        // drags are sent as fast as Prolog answers them, the latest point first
        if (!pending) { pending = [x, y]; requestAnimationFrame(() => { const [px, py] = pending; flush(); if (pressed) this.send(`drag(${px}, ${py})`, px, py); }); } else pending = [x, y];
      } else if (this.rt.handles.has('hover') && !pending) {
        pending = [x, y];
        requestAnimationFrame(() => { const [px, py] = pending; flush(); this.send(`hover(${px}, ${py})`, px, py); });
      }
    });
    const up = (e) => {
      clearTimeout(timer);
      if (!pressed || e.pointerId !== pressed.id) return;
      pressed = null;
      const [x, y] = this.point(e);
      this.send(`up(${x}, ${y})`, x, y);
    };
    st.addEventListener('pointerup', up);
    st.addEventListener('pointercancel', up);
    st.addEventListener('contextmenu', (e) => {
      e.preventDefault();
      const [x, y] = this.point(e);
      this.send(`right(${x}, ${y})`, x, y);
    });
    this.app.addEventListener('keydown', (e) => {
      if (e.target.closest('input, textarea, select')) return;
      if (this.open) { this.menuKey(e); return; }
      const k = KEYS[e.key] ?? (e.key.length === 1 ? e.key.toLowerCase() : null);
      if (!k) return;
      const goal = M.shortcut(this.rt.menu('bar'), k);
      if (goal && (e.ctrlKey || e.metaKey || !e.target.closest('.ps-stage') || k.length === 1)) { e.preventDefault(); this.runGoal(goal); return; }
      if (e.ctrlKey || e.metaKey) return;
      e.preventDefault();
      this.send(`key(${atomText(k)})`);
    });
    document.addEventListener('pointerdown', this.outside = (e) => { if (this.open && !e.target.closest('.ps-menu, .ps-menubar')) this.closeMenus(); }, true);
  }

  send(ev, x, y) {
    const r = this.rt.event(ev, x === undefined ? {} : { x, y });
    if (r.skipped) return;
    this.after(r);
  }
  runGoal(goal) { this.after(this.rt.run(goal)); }
  after(r) {
    this.render();
    this.hooks.ran?.(r);
  }

  // ---- drawing
  render() {
    const rt = this.rt;
    if (rt.dirty.paint) { this.paintRegion(rt.dirty.paint); rt.dirty.paint = null; }
    if (rt.dirty.scene) { this.renderScene(); this.renderPanel(); rt.dirty.scene = false; }
    this.renderOverlay();
    this.stage.style.cursor = rt.pointerCss;
    this.status.textContent = rt.status;
    for (const q of rt.requests.splice(0)) {
      if (q.popup) this.openPopup(q.popup, q.at);
      if (q.save) this.save(q);
    }
  }
  paintRegion(box) {
    const b = this.rt.bitmap;
    const [x0, y0, x1, y1] = box === 'all' ? [0, 0, b.w - 1, b.h - 1] : box;
    for (let y = y0; y <= y1; y++) for (let x = x0, i = y * b.w + x0; x <= x1; x++, i++) {
      const c = b.px[i];
      this.rgba[i] = 0xff000000 | ((c & 0xff) << 16) | (c & 0xff00) | ((c >> 16) & 0xff);
    }
    this.ctx.putImageData(this.image, 0, 0, x0, y0, x1 - x0 + 1, y1 - y0 + 1);
  }
  renderScene() {
    const kids = [];
    let layer = null, g = null;
    for (const it of S.drawn(this.rt.scene)) {
      if (it.layer !== layer) { layer = it.layer; g = s('g', { 'data-layer': layer }); kids.push(g); }
      const [tag, attrs] = element(it);
      g.append(s(tag, { ...attrs, 'data-id': it.id }));
    }
    this.vector.replaceChildren(...kids);
  }
  renderOverlay() {
    const rt = this.rt, sc = rt.scene, kids = [];
    for (const id of sc.selected) {
      if (!sc.nodes[id]) continue;
      const [x, y, w, hh] = S.bounds(sc, id);
      kids.push(s('rect', { x: x - 3, y: y - 3, width: w + 6, height: hh + 6, class: 'ps-sel' }));
    }
    for (const [, x, y] of handles(sc)) kids.push(s('rect', { x: x - HANDLE, y: y - HANDLE, width: 2 * HANDLE, height: 2 * HANDLE, class: 'ps-handle' }));
    if (rt.editor.mode === 'band' && rt.editor.box) { const [x, y, w, hh] = rt.editor.box; kids.push(s('rect', { x, y, width: w, height: hh, class: 'ps-band' })); }
    this.overlay.replaceChildren(...kids);
  }

  // ---- menus: the bar, and pop-ups at the pointer; submenus to any depth
  renderBar() {
    let bar;
    try { bar = this.rt.menu('bar'); } catch { bar = []; }
    this.menubar.replaceChildren(...bar.map((e, i) => h('button', {
      type: 'button', className: 'ps-top', textContent: e.label, role: 'menuitem', ariaHasPopup: 'true',
      onclick: (ev) => {
        if (this.open?.from === 'bar' && this.open.bar === i) { this.closeMenus(); return; }
        const r = ev.currentTarget.getBoundingClientRect();
        this.showMenu({ menu: this.rt.menu('bar')[i].items ?? [], path: [], from: 'bar', bar: i, place: [r.left, r.bottom] });
      },
      onpointerenter: () => { if (this.open?.from === 'bar' && this.open.bar !== i) this.menubar.children[i].click(); }
    })));
    this.menubar.hidden = !bar.length;
  }
  openPopup(name, at) {
    const menu = this.rt.menu(name);
    const r = this.stage.getBoundingClientRect();
    this.showMenu({ menu, path: [], from: 'popup', place: [r.left + at[0] * this.scale, r.top + at[1] * this.scale] });
  }
  showMenu(open) {
    this.open = open;
    this.drawMenus();
  }
  closeMenus() { if (!this.open) return; this.open = null; this.menus.replaceChildren(); }
  drawMenus() {
    const o = this.open;
    if (!o) return;
    this.menus.replaceChildren();
    const ar = viewport();
    // a phone: one panel at a time, the open submenu in place of its menu, with a way back
    if (ar.width < 600) return this.drawDrill(ar);
    let items = o.menu, parent = null, row = null;
    for (let depth = 0; ; depth++) {
      const at = o.path[depth];
      const panel = h('div', { className: 'ps-menu', role: 'menu' },
        ...items.map((e, i) => {
          if (e.type === 'sep') return h('div', { className: 'ps-sep', role: 'separator' });
          const path = [...o.path.slice(0, depth), i];
          return h('button', {
            type: 'button', role: 'menuitem', className: `ps-entry${i === at ? ' on' : ''}${e.type === 'menu' ? ' sub' : ''}`, disabled: e.enabled === false,
            onclick: () => this.chooseEntry(path),
            // redraw only when the open path changes: redrawing the entry under the pointer as it is
            // pressed would lose the click
            onpointerenter: (ev) => { if (ev.pointerType === 'mouse' && e.enabled !== false && String(this.open.path) !== String(path)) { this.open.path = path; this.drawMenus(); } }
          },
          h('span', { className: 'ps-check', textContent: e.checked ? '✓' : '' }),
          h('span', { className: 'ps-label', textContent: e.label }),
          h('span', { className: 'ps-more', textContent: e.type === 'menu' ? '›' : e.key ? e.key.toUpperCase() : '' }));
        }));
      this.menus.append(panel);
      const w = panel.offsetWidth, ht = panel.offsetHeight;
      let left, top;
      if (!parent) [left, top] = o.place;
      else {
        // beside its entry, on the right; on the left of its parent when there's no room
        const pr = parent.getBoundingClientRect();
        left = pr.right - ar.left - 4;
        if (left + w > ar.width) left = Math.max(0, pr.left - ar.left - w + 4);
        top = row.top - ar.top - 4;
      }
      left = Math.max(0, Math.min(left, ar.width - w - 2));
      if (top + ht > ar.height && ht < ar.height) top = Math.max(0, ar.height - ht - 2);
      Object.assign(panel.style, { left: `${left}px`, top: `${top}px` });
      const e = items[at];
      if (at === undefined || e?.type !== 'menu') break;
      parent = panel;
      row = panel.children[at].getBoundingClientRect();
      items = e.items;
    }
  }
  drawDrill(ar) {
    const o = this.open;
    // the deepest open submenu (the path's last index is only highlighted, not opened)
    let items = o.menu, depth = 0, label = null;
    while (depth < o.path.length - 1) { const e = items[o.path[depth]]; if (e?.type !== 'menu') break; label = e.label; items = e.items; depth++; }
    const at = o.path[depth];
    const back = depth > 0 ? h('button', { type: 'button', className: 'ps-entry ps-back', onclick: () => { this.open.path = o.path.slice(0, depth); this.drawMenus(); } },
      h('span', { className: 'ps-check', textContent: '‹' }), h('span', { className: 'ps-label', textContent: label })) : null;
    const panel = h('div', { className: 'ps-menu ps-drill', role: 'menu' }, back, back && h('div', { className: 'ps-sep' }),
      ...items.map((e, i) => {
        if (e.type === 'sep') return h('div', { className: 'ps-sep', role: 'separator' });
        const path = [...o.path.slice(0, depth), i];
        return h('button', { type: 'button', role: 'menuitem', className: `ps-entry${i === at ? ' on' : ''}`, disabled: e.enabled === false, onclick: () => this.chooseEntry(path) },
          h('span', { className: 'ps-check', textContent: e.checked ? '✓' : '' }),
          h('span', { className: 'ps-label', textContent: e.label }),
          h('span', { className: 'ps-more', textContent: e.type === 'menu' ? '›' : '' }));
      }));
    this.menus.append(panel);
    const w = panel.offsetWidth, ht = panel.offsetHeight;
    const left = Math.max(4, Math.min(o.place[0], ar.width - w - 4));
    const top = Math.max(4, Math.min(o.place[1], ar.height - ht - 4));
    Object.assign(panel.style, { left: `${left}px`, top: `${top}px` });
  }
  chooseEntry(path) {
    const r = M.choose(this.open.menu, path);
    if (r.run) { this.closeMenus(); this.runGoal(r.run); this.renderBar(); return; }
    this.open.path = r.path;
    this.drawMenus();
  }
  menuKey(e) {
    const k = KEYS[e.key];
    if (!k || !['up', 'down', 'left', 'right', 'enter', 'escape'].includes(k)) return;
    e.preventDefault();
    const r = M.key(this.open.menu, this.open.path, k);
    if (r.run) { this.closeMenus(); this.runGoal(r.run); this.renderBar(); return; }
    if (r.closed) { this.closeMenus(); return; }
    this.open.path = r.path;
    this.drawMenus();
  }

  // ---- the palette: drag a tile onto the canvas, and the program hears drop(Thing, X, Y)
  renderPalette() {
    this.palette.replaceChildren(...this.rt.decl.palette.map((t) => {
      const tile = h('div', { className: 'ps-tile', title: t.label, role: 'button', tabIndex: 0 }, h('span', { className: 'ps-icon', textContent: t.icon || '▢' }), h('span', { textContent: t.label }));
      tile.addEventListener('pointerdown', (e) => this.dragTile(e, t));
      tile.addEventListener('keydown', (e) => { if (e.key === 'Enter') { const [w, hh] = this.rt.canvasSize; this.send(`drop(${t.thing}, ${Math.round(w / 2)}, ${Math.round(hh / 2)})`); } });
      return tile;
    }));
  }
  dragTile(e, t) {
    e.preventDefault();
    const ghost = h('div', { className: 'ps-ghost', textContent: t.icon || t.label });
    this.app.append(ghost);
    const ar = this.app.getBoundingClientRect();
    const place = (ev) => Object.assign(ghost.style, { left: `${ev.clientX - ar.left}px`, top: `${ev.clientY - ar.top}px` });
    place(e);
    const move = (ev) => place(ev);
    const end = (ev) => {
      removeEventListener('pointermove', move);
      removeEventListener('pointerup', end);
      ghost.remove();
      const r = this.stage.getBoundingClientRect();
      if (ev.clientX >= r.left && ev.clientX <= r.right && ev.clientY >= r.top && ev.clientY <= r.bottom) {
        const [x, y] = this.point(ev);
        this.send(`drop(${t.thing}, ${x}, ${y})`, x, y);
      }
    };
    addEventListener('pointermove', move);
    addEventListener('pointerup', end);
  }

  // ---- the layers panel: each layer and the shapes and groups in it, top first. What you
  // do here runs Prolog commands, so it shows in the trace like everything else.
  renderPanel() {
    if (!this.rt.decl.panels.includes('layers')) return;
    const sc = this.rt.scene;
    const item = (n, depth) => h('div', {},
      h('button', { type: 'button', className: `ps-node${sc.selected.includes(n.id) ? ' on' : ''}`, style: `padding-left:${8 + depth * 14}px`, textContent: `${n.kind === 'group' ? '▾ ' : ''}${n.id}`, title: n.kind, onclick: () => this.runGoal(`select([${n.id}])`) }),
      ...(n.items ?? []).map((c) => item(c, depth + 1)));
    this.panel.replaceChildren(h('div', { className: 'ps-panel-title', textContent: 'Layers' }),
      ...S.tree(sc).map((l) => h('div', { className: `ps-layer${l.active ? ' active' : ''}` },
        h('div', { className: 'ps-layer-row' },
          h('button', { type: 'button', className: 'ps-eye', title: l.shown ? 'Hide' : 'Show', textContent: l.shown ? '👁' : '–', onclick: () => this.runGoal(`show_layer(${l.id}, ${!l.shown})`) }),
          h('button', { type: 'button', className: 'ps-lock', title: l.locked ? 'Unlock' : 'Lock', textContent: l.locked ? '🔒' : '🔓', onclick: () => this.runGoal(`lock_layer(${l.id}, ${!l.locked})`) }),
          h('button', { type: 'button', className: 'ps-lname', textContent: l.name, onclick: () => this.runGoal(`use_layer(${l.id})`) })),
        ...l.items.map((n) => item(n, 1)))));
  }

  // ---- saving: a picture (PNG of the paint and the shapes) or a drawing (SVG)
  async save(q) {
    const [w, hgt] = this.rt.canvasSize;
    const name = q.name.replace(/[^\w.\- ]/g, '_') || 'untitled';
    if (q.save === 'drawing') { this.hooks.save?.(`${name.replace(/\.svg$/, '')}.svg`, sceneSvg(this.rt.scene, w, hgt), 'image/svg+xml'); return; }
    const c = h('canvas', { width: w, height: hgt });
    const x = c.getContext('2d');
    x.drawImage(this.paintCanvas, 0, 0);
    const img = new Image();
    await new Promise((res) => { img.onload = res; img.onerror = res; img.src = `data:image/svg+xml,${encodeURIComponent(sceneSvg(this.rt.scene, w, hgt))}`; });
    x.drawImage(img, 0, 0);
    c.toBlob((blob) => this.hooks.save?.(`${name.replace(/\.png$/, '')}.png`, blob, 'image/png'), 'image/png');
  }

  destroy() {
    this.ro?.disconnect();
    document.removeEventListener('pointerdown', this.outside, true);
    this.root.replaceChildren();
  }
}

// mount a program in an element: what the app, the tutes and Visual Starlog's slides use
export async function mount(root, source, { P, Runtime, hooks = {} } = {}) {
  const rt = new Runtime(P);
  const loaded = rt.load(source);
  if (loaded.error && !rt.it?.prog) throw new Error(loaded.error);
  const view = new View(root, rt, hooks);
  if (loaded.start) hooks.ran?.(loaded.start);
  return { rt, view, loaded };
}
