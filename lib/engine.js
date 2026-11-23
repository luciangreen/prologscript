// The Prolog engine: pl2detlog's interpreter (vendor/pl2detlog.js), loaded once per page.
let loading = null;
export function engine(src = new URL('../vendor/pl2detlog.js', import.meta.url).href) {
  if (globalThis.PL2D?.Interpreter) return Promise.resolve(globalThis.PL2D);
  return (loading ??= new Promise((resolve, reject) => {
    const s = Object.assign(document.createElement('script'), { src, async: true });
    s.onload = () => (globalThis.PL2D?.Interpreter ? resolve(globalThis.PL2D) : reject(new Error("the Prolog engine didn't start")));
    s.onerror = () => { loading = null; reject(new Error("couldn't load the Prolog engine")); };
    document.head.append(s);
  }));
}
