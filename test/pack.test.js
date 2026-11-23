// The pack (scripts/pack.mjs): one file for the app, one drop-in script, and a zip of both. Needs
// esbuild ($ESBUILD or `npm install`); without it the test is skipped.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { createRequire } from 'node:module';
import { execFileSync } from 'node:child_process';

let have = true;
try { createRequire(import.meta.url).resolve(process.env.ESBUILD || 'esbuild'); } catch { have = false; }
const dist = new URL('../dist/', import.meta.url);
const read = (f) => fs.readFileSync(new URL(f, dist), 'utf8');

test('the pack carries everything inside it', { skip: !have && 'esbuild is not installed' }, async () => {
  const { pack, files } = await import('../scripts/pack.mjs');
  await pack();
  const html = read('prologscript.html');
  const markup = html.replace(/(<(script|style)[^>]*>)[\s\S]*?(<\/\2>)/g, '$1$3');
  assert.doesNotMatch(markup, /(src|href)="(?!data:|#|https?:)/, 'the one-file app points at no other file');
  assert.doesNotMatch(markup, /type="module"/);
  for (const [rel, text] of Object.entries(files())) assert.ok(html.includes(JSON.stringify(text).slice(1, 60)), `${rel} is in the one-file app`);
  assert.equal(Object.keys(files()).length, 13, 'two demos and eleven tutes');
  assert.match(html, /PL2D/);
  const js = read('prologscript.js');
  assert.match(js, /globalThis\.PS_CSS = /);
  assert.match(js, /globalThis\.PrologScript = /);
  assert.match(read('example.html'), /<script type="text\/prolog">/);
  const list = execFileSync('unzip', ['-Z1', new URL('prologscript-pack.zip', dist).pathname], { encoding: 'utf8' }).split('\n');
  for (const f of ['prologscript.html', 'prologscript.js', 'example.html', 'README.txt', 'LICENSE', 'demos/paint.pl', 'demos/draw.pl', 'tutes/menus.pl']) assert.ok(list.includes(f), `${f} is in the zip`);
});
