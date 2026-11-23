// Reads one of PrologScript's own text files (demos/*.pl, tutes/*.pl). In the pack, the files are
// built into the page as globalThis.PS_FILES, so it works offline and from file://; otherwise they
// are fetched from beside the app.
export function readText(rel, base) {
  const built = globalThis.PS_FILES?.[rel];
  if (typeof built === 'string') return Promise.resolve(built);
  return fetch(new URL(rel, base ?? document.baseURI)).then((r) => {
    if (!r.ok) throw new Error(`couldn't read ${rel}`);
    return r.text();
  });
}
