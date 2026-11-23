// The tutes: one for each element of PrologScript. A tute is a PrologScript file (tutes/*.pl):
// lesson(N, Title, Says) and check(N, Hint, Goal) facts, and each step's program between
// :- begin(N). and :- end(N). A step's check is a Prolog goal run in the learner's program.
import { Runtime } from './runtime.js';

export const TUTES = [
  { id: 'menus', title: 'Menus', about: 'A menu bar, menus inside menus, ticks and shortcuts', steps: 3 },
  { id: 'popups', title: 'Pop-up menus', about: 'Right-click or hold a finger down; pop-ups inside pop-ups', steps: 3 },
  { id: 'events', title: 'Events', about: 'on/1: down, drag, up, keys, and say', steps: 3 },
  { id: 'painting', title: 'Painting', about: 'Brushes, lines, fill, spray and undo', steps: 3 },
  { id: 'shapes', title: 'Vector shapes', about: 'Rectangles, circles, lines, polygons and text', steps: 3 },
  { id: 'groups', title: 'Groups', about: 'Shapes in groups, groups in groups: levels', steps: 3 },
  { id: 'layers', title: 'Layers', about: 'Back and front, hide, lock, move between layers', steps: 3 },
  { id: 'editor', title: 'The editor', about: 'Select, move, resize and select many with edit/1', steps: 3 },
  { id: 'dragdrop', title: 'Drag and drop', about: 'A palette, drop events, and dragging into a bin', steps: 3 },
  { id: 'pointers', title: 'Pointers', about: 'System pointers, brush rings, glyphs and SVG', steps: 3 },
  { id: 'state', title: 'State and visible code', about: 'Remembering things, and seeing what ran', steps: 3 }
];

// a tute file -> { title, steps: [{ n, title, says, hint, check, code }] }
export function parseTute(P, text) {
  const blocks = new Map();
  const rest = text.replace(/^:- begin\((\d+)\)\.[ \t]*\n([\s\S]*?)^:- end\(\1\)\.[ \t]*$/gm, (_, n, body) => { blocks.set(Number(n), body.replace(/\s+$/, '\n')); return ''; });
  const rt = new Runtime(P);
  const loaded = rt.load(rest);
  if (!loaded.ok && loaded.error) throw new Error(`the tute didn't load: ${loaded.error}`);
  const q = rt.query('forall(tute(T, A), ps_note(tute(T, A))), forall(lesson(N, T, S), ps_note(lesson(N, T, S))), forall(check(N, H, G), ps_note(check(N, H, G)))');
  if (q.error) throw new Error(q.error);
  const tute = q.notes.find((x) => x.f === 'tute');
  const checks = new Map(q.notes.filter((x) => x.f === 'check').map((x) => [x.a[0], { hint: String(x.a[1]), check: typeof x.a[2] === 'string' ? x.a[2] : x.a[2].text }]));
  const steps = q.notes.filter((x) => x.f === 'lesson').map((x) => ({ n: x.a[0], title: String(x.a[1]), says: String(x.a[2]), ...checks.get(x.a[0]), code: blocks.get(x.a[0]) ?? '' }));
  return { title: tute ? String(tute.a[0]) : 'Tute', about: tute ? String(tute.a[1]) : '', steps: steps.sort((a, b) => a.n - b.n) };
}

const cache = new Map();
export async function loadTute(P, id) {
  if (!TUTES.some((t) => t.id === id)) throw new Error(`there is no tute called ${id}`);
  if (!cache.has(id)) cache.set(id, fetch(new URL(`../tutes/${id}.pl`, import.meta.url)).then((r) => r.text()).then((t) => parseTute(P, t)));
  return cache.get(id);
}
