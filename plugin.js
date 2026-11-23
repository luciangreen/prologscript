// PrologScript as a plug-in: other apps (Visual Starlog's slides) run a program in an element.
//
//   import { mountProgram } from '../prologscript/plugin.js';
//   const ps = await mountProgram(element, source, { code: true });   // ps.destroy() to stop it
//
// The element gets the running program and, with code: true, a "Code" fold showing its source and
// the clause that last ran. Saving a picture or drawing downloads it.
import { engine } from './lib/engine.js';
import { Runtime } from './lib/runtime.js';
import { View } from './lib/view.js';

let styled = false;
function style() {
  if (styled) return;
  styled = true;
  document.head.append(Object.assign(document.createElement('link'), { rel: 'stylesheet', href: new URL('./lib/view.css', import.meta.url).href }));
}
const h = (tag, props = {}, ...kids) => { const e = Object.assign(document.createElement(tag), props); e.append(...kids); return e; };

export async function mountProgram(el, source, { code = true, title } = {}) {
  style();
  const P = await engine();
  const rt = new Runtime(P);
  const loaded = rt.load(source);
  const host = h('div', { className: 'ps-plugin' });
  const pre = h('pre', { className: 'ps-plugin-code' });
  const lines = source.split('\n');
  const showCode = (marked = []) => {
    pre.replaceChildren(...lines.map((l, i) => h('span', { className: marked.some((c) => i + 1 >= c.from && i + 1 <= c.to) ? 'ps-ran' : '', textContent: `${l}\n` })));
  };
  const status = h('p', { className: 'ps-plugin-note' });
  el.replaceChildren(host, ...(code ? [h('details', { className: 'ps-plugin-fold' }, h('summary', { textContent: title ? `Code: ${title}` : 'Code' }), pre)] : []), status);
  if (loaded.error && !rt.clauses) { status.textContent = `The program didn't load: ${loaded.error}`; return { rt, destroy() {} }; }
  const download = (name, data, type) => {
    const a = h('a', { href: URL.createObjectURL(data instanceof Blob ? data : new Blob([data], { type })), download: name });
    document.body.append(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  };
  const view = new View(host, rt, {
    ran: (r) => { if (code && !/^on\((drag|hover)\(/.test(r.goal)) showCode(rt.clausesFor(r.goal)); status.textContent = r.error ? `✗ ${r.error}` : ''; },
    save: download
  });
  if (code) showCode(loaded.start ? rt.clausesFor('on(start)') : []);
  if (loaded.error) status.textContent = `✗ ${loaded.error}`;
  return { rt, view, destroy: () => view.destroy() };
}
