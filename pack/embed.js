// prologscript.js, the pack's drop-in script: PrologScript on any web page, with no LucianOS and
// no server. The Prolog engine and the styles are inside it.
//
//   <script src="prologscript.js"></script>
//   <script type="text/prolog">
//     canvas(400, 300, white).
//     on(down(X, Y)) :- paint(dot(X, Y)).
//   </script>
//
// Each <script type="text/prolog"> becomes the running program, in its place. Attributes:
//   data-src="paint.pl"   read the program from a file instead (needs the page to be served)
//   data-code="false"     hide the code fold under the program
// From JavaScript: PrologScript.mountProgram(element, source, { code: true }).
import { mountProgram } from '../plugin.js';

async function mountScripts(root = document) {
  const out = [];
  for (const s of root.querySelectorAll('script[type="text/prolog"]:not([data-mounted])')) {
    s.dataset.mounted = 'yes';
    const el = document.createElement('div');
    el.className = 'prologscript';
    s.after(el);
    try {
      const source = s.dataset.src ? await (await fetch(s.dataset.src)).text() : s.textContent.replace(/^\n/, '');
      out.push(await mountProgram(el, source, { code: s.dataset.code !== 'false', title: s.dataset.title }));
    } catch (e) {
      el.textContent = `PrologScript: ${e.message}`;
      el.style.cssText = 'color:#b00020;font:14px system-ui';
    }
  }
  return out;
}

globalThis.PrologScript = { mountProgram, mountScripts, version: __PS_VERSION__ };
if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', () => mountScripts());
else mountScripts();
