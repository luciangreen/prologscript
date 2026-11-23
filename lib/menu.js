// Hierarchical menus, for the menu bar and pop-up menus. Pure: proofs/spec.pl states the same.
//
// A menu is a list of entries:
//   { type: 'item', label, goal, key?, enabled?, checked? }   (goal: Prolog text to run)
//   { type: 'menu', label, items: [...] }                       (a submenu, to any depth)
//   { type: 'sep' }
// The open state is a path of indices: [] nothing open, [2] entry 2 highlighted, [2, 0] its
// submenu open with entry 0 highlighted.

export const usable = (e) => !!e && e.type !== 'sep' && e.enabled !== false;

export function at(menu, path) {
  let items = menu, e = null;
  for (const i of path) {
    if (!Array.isArray(items)) return null;
    e = items[i];
    if (!e) return null;
    items = e.type === 'menu' ? e.items : null;
  }
  return e;
}
const listAt = (menu, path) => (path.length === 0 ? menu : at(menu, path)?.items ?? null);

// the next usable entry after i in a direction, wrapping; -1 if there is none
export function step(items, i, dir) {
  const n = items.length;
  for (let k = 1; k <= n; k++) {
    const j = (((i + dir * k) % n) + n) % n;
    if (usable(items[j])) return j;
  }
  return -1;
}
const first = (items) => step(items, -1, 1);

// a key on an open menu: up, down, right (open a submenu), left (close one), enter, escape.
// -> { path, run?: goal, closed?: true }
export function key(menu, path, k) {
  if (path.length === 0) {
    if (k === 'down' || k === 'enter' || k === 'right') { const f = first(menu); return f < 0 ? { path: [] } : { path: [f] }; }
    return { path: [] };
  }
  const parent = path.slice(0, -1), i = path[path.length - 1];
  const items = listAt(menu, parent);
  const e = items?.[i];
  switch (k) {
    case 'down': case 'up': { const j = step(items, i, k === 'down' ? 1 : -1); return { path: j < 0 ? path : [...parent, j] }; }
    case 'right': case 'enter':
      if (e?.type === 'menu') { const f = first(e.items); return { path: f < 0 ? path : [...path, f] }; }
      if (k === 'enter' && usable(e)) return { path: [], run: e.goal, closed: true };
      return { path };
    case 'left': return parent.length ? { path: parent } : { path };
    case 'escape': return parent.length ? { path: parent } : { path: [], closed: true };
    default: return { path };
  }
}

// choosing an entry by its path (a click or tap): an item runs; a submenu opens
export function choose(menu, path) {
  const e = at(menu, path);
  if (!usable(e)) return { path: path.slice(0, -1) };
  if (e.type === 'menu') { const f = first(e.items); return { path: f < 0 ? path : [...path, f] }; }
  return { path: [], run: e.goal, closed: true };
}

// a keyboard shortcut: the first usable item with that key, anywhere in the menus
export function shortcut(menus, k) {
  const look = (items) => {
    for (const e of items) {
      if (e.type === 'item' && usable(e) && e.key && e.key.toLowerCase() === k.toLowerCase()) return e.goal;
      if (e.type === 'menu' && e.enabled !== false) { const g = look(e.items); if (g) return g; }
    }
    return null;
  };
  return look(menus);
}

// every item's path and label, depth first ("Colour › Warm › Red")
export function paths(menu, pre = [], names = []) {
  const out = [];
  menu.forEach((e, i) => {
    if (e.type === 'item') out.push({ path: [...pre, i], label: [...names, e.label].join(' › '), goal: e.goal });
    if (e.type === 'menu') out.push(...paths(e.items, [...pre, i], [...names, e.label]));
  });
  return out;
}

export const depth = (menu) => Math.max(0, ...menu.map((e) => (e.type === 'menu' ? 1 + depth(e.items) : 1)));
