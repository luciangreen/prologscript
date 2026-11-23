import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { makeIos, toText } from '../io/engine.mjs';
import { cases, title } from '../io/cases.mjs';

const read = (f) => fs.readFileSync(new URL(`../io/${f}`, import.meta.url), 'utf8');

test('the 200 recorded inputs give the same outputs', async () => {
  const saved = read('ios.jsonl').trim().split('\n').map((l) => JSON.parse(l));
  assert.equal(saved.length, 200);
  const now = await makeIos(cases);
  for (let i = 0; i < saved.length; i++) assert.deepEqual(now[i], saved[i], `example ${i + 1} (${saved[i].name}) changed`);
  assert.equal(read('ios.txt'), toText(now, title));
});
