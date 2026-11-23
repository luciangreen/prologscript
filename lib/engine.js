// The Prolog engine: pl2detlog's interpreter (vendor/pl2detlog.js), loaded once per page.
let loading = null;
// (In the pack the engine is already in the page, so no URL is needed.)
export function engine(src) {
  if (globalThis.PL2D?.Interpreter) return Promise.resolve(globalThis.PL2D);
  src ??= new URL('../vendor/pl2detlog.js', import.meta.url).href;
  return (loading ??= new Promise((resolve, reject) => {
    const s = Object.assign(document.createElement('script'), { src, async: true });
    s.onload = () => (globalThis.PL2D?.Interpreter ? resolve(globalThis.PL2D) : reject(new Error("the Prolog engine didn't start")));
    s.onerror = () => { loading = null; reject(new Error("couldn't load the Prolog engine")); };
    document.head.append(s);
  }));
}
