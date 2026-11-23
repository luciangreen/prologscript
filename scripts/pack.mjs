// Builds the pack: PrologScript to use outside LucianOS, with nothing to install.
//
//   dist/prologscript.html       the whole app (Paint, Draw, the tutes, My program) in one file:
//                                open it from a folder, a USB stick or any web host, offline
//   dist/prologscript.js         the drop-in script: PrologScript programs in any web page
//   dist/example.html            a page that uses prologscript.js
//   dist/prologscript-pack.zip   all of these, the demos and tutes as .pl files, and the licence
//
//   node scripts/pack.mjs [--esbuild path/to/esbuild]
// esbuild comes from --esbuild, $ESBUILD, or `npm install` (a dev dependency).
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const OUT = path.join(root, 'dist');
const read = (f) => fs.readFileSync(path.join(root, f), 'utf8');
const arg = process.argv.indexOf('--esbuild');
const esbuild = createRequire(import.meta.url)(arg > 0 ? path.resolve(process.argv[arg + 1]) : process.env.ESBUILD || 'esbuild');
const { version } = JSON.parse(read('package.json'));

// text that is safe inside <script> and <style>
const inScript = (s) => s.replace(/<\/(script)/gi, '<\\/$1');
const inStyle = (s) => s.replace(/<\/(style)/gi, '<\\/$1');

// the program files the app reads, by the path it asks for
export function files() {
  const out = {};
  for (const dir of ['demos', 'tutes']) for (const f of fs.readdirSync(path.join(root, dir)).filter((f) => f.endsWith('.pl')).sort()) out[`${dir}/${f}`] = read(`${dir}/${f}`);
  return out;
}

async function bundle(entry) {
  const r = await esbuild.build({
    entryPoints: [path.join(root, entry)], bundle: true, write: false, format: 'iife', target: 'es2020', charset: 'utf8',
    define: { 'import.meta.url': 'document.baseURI', __PS_VERSION__: JSON.stringify(version) }, logLevel: 'error'
  });
  return r.outputFiles[0].text;
}

export async function pack() {
  fs.rmSync(OUT, { recursive: true, force: true });
  fs.mkdirSync(OUT, { recursive: true });
  const engine = read('vendor/pl2detlog.js');
  const css = read('lib/view.css');
  const head = `/* PrologScript ${version}, the pack: github.com/luciangreen/prologscript. BSD-3-Clause. Includes pl2detlog (BSD-3-Clause). */\n`;

  // 1. the app in one file
  const app = await bundle('app.js');
  let html = read('index.html');
  // (functions as replacements, so a $ in the engine's text is kept as it is)
  const swap = (s, from, to) => { if (!s.includes(from)) throw new Error(`index.html has no ${from}`); return s.replace(from, () => to); };
  html = swap(html, '<link rel="stylesheet" href="lib/view.css">', `<style>\n${inStyle(css)}</style>`);
  html = swap(html, '<link rel="stylesheet" href="style.css">', `<style>\n${inStyle(read('style.css'))}</style>`);
  html = swap(html, '<script type="module" src="app.js"></script>',
    `<script>\n${inScript(engine)}</script>\n<script>globalThis.PS_FILES = ${inScript(JSON.stringify(files()))};</script>\n<script>\n${inScript(head + app)}</script>`);
  html = swap(html, '<title>PrologScript</title>', `<title>PrologScript</title>\n<meta name="generator" content="PrologScript ${version} pack">`);
  // every tag that loads something must carry it inside (a script's text is left out of the check)
  const markup = html.replace(/(<(script|style)[^>]*>)[\s\S]*?(<\/\2>)/g, '$1$3');
  if (/(src|href)="(?!data:|#|https?:)/.test(markup)) throw new Error('the one-file app still points at another file');
  fs.writeFileSync(path.join(OUT, 'prologscript.html'), html);

  // 2. the drop-in script
  const embed = await bundle('pack/embed.js');
  fs.writeFileSync(path.join(OUT, 'prologscript.js'), `${head}${engine}\n;globalThis.PS_CSS = ${JSON.stringify(css)};\n${embed}`);
  fs.writeFileSync(path.join(OUT, 'example.html'), read('pack/example.html'));

  // 3. the zip
  const stage = path.join(OUT, 'prologscript-pack');
  fs.mkdirSync(stage);
  for (const f of ['prologscript.html', 'prologscript.js', 'example.html']) fs.copyFileSync(path.join(OUT, f), path.join(stage, f));
  for (const [rel, text] of Object.entries(files())) {
    fs.mkdirSync(path.join(stage, path.dirname(rel)), { recursive: true });
    fs.writeFileSync(path.join(stage, rel), text);
  }
  fs.copyFileSync(path.join(root, 'LICENSE'), path.join(stage, 'LICENSE'));
  fs.writeFileSync(path.join(stage, 'README.txt'), read('pack/README.txt').replaceAll('{{version}}', version));
  execFileSync('zip', ['-qrX', '../prologscript-pack.zip', '.'], { cwd: stage });
  fs.rmSync(stage, { recursive: true });
  fs.writeFileSync(path.join(OUT, 'release-notes.md'), [
    `PrologScript ${version}, the pack: PrologScript on its own, without LucianOS, offline, with nothing to install.`, '',
    '- **prologscript.html**: the whole app (the Paint and Draw demos with their code, a tute for each part, My program) in one file. Open it from a folder or put it on any web host.',
    '- **prologscript.js**: PrologScript programs in your own pages, written in `<script type="text/prolog">`.',
    '- **prologscript-pack.zip**: both, an example page, the demos and tutes as .pl files, and the licence.', ''].join('\n'));
  return fs.readdirSync(OUT).filter((f) => f !== 'release-notes.md').map((f) => `${f} (${Math.round(fs.statSync(path.join(OUT, f)).size / 1024)} KB)`);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) console.log(`built dist/: ${(await pack()).join(', ')}`);
