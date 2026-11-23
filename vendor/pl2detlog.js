/* pl2detlog library — Prolog to Detlog. BSD-3-Clause. github.com/luciangreen/pl2detlog */
/* pl2detlog core: terms, reader (tokenizer + operator-precedence parser), printer.
   BSD-3-Clause. Part of pl2detlog (Prolog -> Detlog). */
(function (P) {
  'use strict';

  // ---------- terms ----------
  let varCounter = 0;
  const atomTable = new Map();
  function Atom(n) { let a = atomTable.get(n); if (!a) { a = { t: 'a', n }; atomTable.set(n, a); } return a; }
  // Integers are unbounded, as in SWI-Prolog: a JS number while it is a safe integer, a BigInt beyond
  // (always the one or the other for a given value, so === compares them). Floats are JS numbers.
  function Num(v, f) { if (typeof v === 'bigint') return Int(v); return { t: 'n', v, f: !!f || !Number.isInteger(v) }; }
  function Int(v) { if (typeof v === 'bigint') { if (v >= -9007199254740991n && v <= 9007199254740991n) v = Number(v); } else if (!Number.isSafeInteger(v) && Number.isInteger(v)) v = BigInt(v); return { t: 'n', v, f: false }; }
  function Str(v) { return { t: 's', v }; }
  function Var(name) { return { t: 'v', name: name || null, ref: null, id: ++varCounter }; }
  function Cmp(f, a) { return a.length === 0 ? Atom(f) : { t: 'c', f, a }; }
  const NIL = Atom('[]');
  const TRUE = Atom('true');
  const FAIL = Atom('fail');
  function cons(h, t) { return { t: 'c', f: '.', a: [h, t] }; }
  // a dict: dict(Tag, [K-V, ...]) with keys (atoms or small integers) in standard order, each once
  function mkDict(tag, pairs) {
    const ps = pairs.map(([k, v]) => [deref(k), v]);
    for (const [k] of ps) if (!(k.t === 'a' || k.t === 'n' && !k.f)) throw new Error('dict keys are atoms or integers');
    ps.sort((x, y) => compare(x[0], y[0]));
    for (let i = 1; i < ps.length; i++) if (compare(ps[i - 1][0], ps[i][0]) === 0) throw new PrologSyntaxError('duplicate dict key ' + show(ps[i][0]), 0, '');
    return { t: 'c', f: 'dict', a: [tag, list(ps.map(([k, v]) => ({ t: 'c', f: '-', a: [k, v] })))] };
  }
  function dictPairs(t) { t = deref(t); if (t.t !== 'c' || t.f !== 'dict' || t.a.length !== 2) return null; const l = listToArray(t.a[1]); if (!l) return null; const out = []; for (const x of l) { const p = deref(x); if (p.t !== 'c' || p.f !== '-' || p.a.length !== 2) return null; out.push([deref(p.a[0]), p.a[1]]); } return out; }
  function list(arr, tail) { let r = tail || NIL; for (let i = arr.length - 1; i >= 0; i--) r = cons(arr[i], r); return r; }

  function deref(t) { while (t.t === 'v' && t.ref) t = t.ref; return t; }
  function isCons(t) { return t.t === 'c' && t.f === '.' && t.a.length === 2; }
  function isNil(t) { return t.t === 'a' && t.n === '[]'; }
  function listToArray(t) { // returns array or null if not proper list
    const out = []; t = deref(t);
    while (isCons(t)) { out.push(t.a[0]); t = deref(t.a[1]); }
    return isNil(t) ? out : null;
  }
  function name(t) { t = deref(t); return t.t === 'a' ? t.n : t.t === 'c' ? t.f : null; }
  function arity(t) { t = deref(t); return t.t === 'c' ? t.a.length : 0; }
  function key(t) { t = deref(t); return t.t === 'a' ? t.n + '/0' : t.t === 'c' ? t.f + '/' + t.a.length : null; }
  function args(t) { t = deref(t); return t.t === 'c' ? t.a : []; }

  // full dereferenced copy with fresh variables (sharing preserved)
  // copy with fresh variables; ground subterms are shared, not copied (they are immutable)
  function copy(t, map) {
    map = map || new Map();
    t = deref(t);
    if (t.gr) return t;
    if (t.t === 'v') { let v = map.get(t); if (!v) { v = Var(t.name); map.set(t, v); } else if (v === t) map.kept = (map.kept || 0) + 1; return v; }
    if (t.t === 'c') {
      if (t.f === '.' && t.a.length === 2) { // iterate along list spines
        // a variable the caller mapped to itself (kept shared, e.g. yall Free) is copied as itself: the
        // cell is unchanged but not ground, so it is shared without the ground mark
        const heads = [], cells = [], kept = []; let x = t;
        while (x.t === 'c' && x.f === '.' && x.a.length === 2 && !x.gr) { cells.push(x); const k0 = map.kept || 0; heads.push(copy(x.a[0], map)); kept.push((map.kept || 0) !== k0); x = deref(x.a[1]); }
        const k1 = map.kept || 0; let r = copy(x, map); let g = (map.kept || 0) === k1;
        for (let i = heads.length - 1; i >= 0; i--) {
          const c = cells[i]; g = g && !kept[i];
          if (r === c.a[1] && heads[i] === c.a[0]) { if (g) c.gr = true; r = c; } // unchanged suffix: share (deref'd tail identical)
          else r = { t: 'c', f: '.', a: [heads[i], r] };
        }
        return r;
      }
      const a = new Array(t.a.length); let same = true; const k0 = map.kept || 0;
      for (let i = 0; i < a.length; i++) { a[i] = copy(t.a[i], map); if (a[i] !== t.a[i]) same = false; }
      if (same) { if ((map.kept || 0) === k0) t.gr = true; return t; }
      return { t: 'c', f: t.f, a };
    }
    return t;
  }
  // resolve all bindings (no fresh vars)
  // resolve bindings; ground subterms are shared and marked ground (t.gr), so later copies are O(1)
  function resolve(t) {
    t = deref(t);
    if (t.t !== 'c' || t.gr) return t;
    if (t.f === '.' && t.a.length === 2) {
      const heads = [], cells = []; let x = t;
      while (x.t === 'c' && x.f === '.' && x.a.length === 2 && !x.gr) { cells.push(x); heads.push(resolve(x.a[0])); x = deref(x.a[1]); }
      let r = resolve(x);
      let g = r.t !== 'v' && (r.t !== 'c' || r.gr === true);
      for (let i = heads.length - 1; i >= 0; i--) {
        const h = heads[i], c = cells[i];
        g = g && h.t !== 'v' && (h.t !== 'c' || h.gr === true);
        if (h === c.a[0] && r === c.a[1]) { if (g) c.gr = true; r = c; }
        else { r = { t: 'c', f: '.', a: [h, r] }; if (g) r.gr = true; }
      }
      return r;
    }
    const a = new Array(t.a.length); let ch = false, g = true;
    for (let i = 0; i < a.length; i++) { const x = resolve(t.a[i]); a[i] = x; if (x !== t.a[i]) ch = true; if (x.t === 'v' || (x.t === 'c' && !x.gr)) g = false; }
    const r = ch ? { t: 'c', f: t.f, a } : t;
    if (g) r.gr = true;
    return r;
  }
  function termVars(t, acc, seen) {
    acc = acc || []; seen = seen || new Set();
    const st = [t]; let n = 0, done = null;
    while (st.length) {
      let x = deref(st.pop());
      if (x.t === 'v') { if (!seen.has(x)) { seen.add(x); acc.push(x); } }
      else if (x.t === 'c' && !x.gr) {
        // a large term may share subterms (or be cyclic): after many steps each compound is visited once
        if (++n > 50000) { done = done || new Set(); if (done.has(x)) continue; done.add(x); }
        for (let i = x.a.length - 1; i >= 0; i--) st.push(x.a[i]);
      }
    }
    return acc;
  }
  function isGround(t) {
    const st = [t]; let n = 0, done = null;
    while (st.length) {
      const x = deref(st.pop()); if (x.t === 'v') return false;
      if (x.t === 'c' && !x.gr) { if (++n > 50000) { done = done || new Set(); if (done.has(x)) continue; done.add(x); } for (const y of x.a) st.push(y); }
    }
    return true;
  }

  // ---------- standard order ----------
  function typeRank(t) { switch (t.t) { case 'v': return 0; case 'n': return 1; case 'a': return 3; case 's': return 4; default: return 5; } }
  function compare(a, b) {
    a = deref(a); b = deref(b);
    if (a === b) return 0;
    const ra = typeRank(a), rb = typeRank(b);
    if (ra !== rb) return ra < rb ? -1 : 1;
    switch (a.t) {
      case 'v': return a.id < b.id ? -1 : 1;
      case 'n': if (a.v !== b.v) return a.v < b.v ? -1 : 1; if (a.f !== b.f) return a.f ? -1 : 1; return 0;
      case 'a': return a.n < b.n ? -1 : a.n > b.n ? 1 : 0;
      case 's': return a.v < b.v ? -1 : a.v > b.v ? 1 : 0;
      case 'c':
        if (a.a.length !== b.a.length) return a.a.length < b.a.length ? -1 : 1;
        if (a.f !== b.f) return a.f < b.f ? -1 : 1;
        for (let i = 0; i < a.a.length; i++) { const c = compare(a.a[i], b.a[i]); if (c) return c; }
        return 0;
    }
    return 0;
  }
  // variant key: canonical string, variables numbered by first occurrence
  function variantKey(t) {
    const m = new Map(); let n = 0; const parts = [];
    (function walk(x) {
      x = deref(x);
      switch (x.t) {
        case 'v': { let k = m.get(x); if (k === undefined) { k = n++; m.set(x, k); } parts.push('_' + k); break; }
        case 'n': parts.push((x.f ? 'f' : 'i') + x.v); break;
        case 'a': parts.push('a' + JSON.stringify(x.n)); break;
        case 's': parts.push('s' + JSON.stringify(x.v)); break;
        case 'c': parts.push('c' + JSON.stringify(x.f) + x.a.length + '('); for (const y of x.a) walk(y); parts.push(')'); break;
      }
    })(t);
    return parts.join(' ');
  }

  // ---------- operators ----------
  const ops = {
    prefix: new Map(), infix: new Map(), postfix: new Map()
  };
  function addOp(p, type, nm) {
    const tbl = type.length === 2 ? (type[0] === 'f' ? ops.prefix : ops.postfix) : ops.infix;
    if (p === 0) tbl.delete(nm); else tbl.set(nm, { p, type });
  }
  [[1200, 'xfx', [':-', '-->']], [1200, 'fx', [':-', '?-']], [1100, 'xfy', [';', '|']], [1105, 'xfy', ['|']],
   [1050, 'xfy', ['->', '*->']], [1000, 'xfy', [',']], [990, 'xfx', [':=']], [900, 'fy', ['\\+']],
   [700, 'xfx', ['=', '\\=', '==', '\\==', '@<', '@>', '@=<', '@>=', '=..', 'is', '=:=', '=\\=', '<', '>', '=<', '>=', '>:<', ':<', 'as', '=@=', '\\=@=']],
   [600, 'xfy', [':']], [500, 'yfx', ['+', '-', '/\\', '\\/', 'xor']], [500, 'fx', ['?']],
   [400, 'yfx', ['*', '/', '//', 'rem', 'mod', 'div', '<<', '>>', 'divmod', 'rdiv']],
   [200, 'xfx', ['**']], [200, 'xfy', ['^']], [200, 'fy', ['-', '+', '\\']], [100, 'yfx', ['.']], [1, 'fx', ['$']],
   [1150, 'fx', ['dynamic', 'discontiguous', 'initialization', 'module_transparent', 'multifile', 'public', 'thread_local', 'table', 'meta_predicate']], [200, 'xfy', ['::']], [100, 'fx', ['@']]
  ].forEach(([p, ty, ns]) => ns.forEach(n => addOp(p, ty, n)));
  ops.infix.set(',', { p: 1000, type: 'xfy' });

  // ---------- tokenizer ----------
  const SYM = '+-*/\\^<>=~:.?@#&$';
  // non-ASCII as SWI-Prolog reads it: letters and digits join names, other symbols join symbol atoms
  const isSym = c => SYM.indexOf(c) >= 0 || c > '\x7f' && /[\p{S}\p{Po}\p{Pd}]/u.test(c) && c !== '\u00b7';
  const isAlnum = c => /[A-Za-z0-9_]/.test(c) || c > '\x7f' && /[\p{L}\p{N}\p{Mn}\p{Mc}]/u.test(c);
  function PrologSyntaxError(msg, pos, src) {
    const line = src ? src.slice(0, pos).split('\n').length : 0;
    const e = new Error('Syntax error' + (line ? ' (line ' + line + ')' : '') + ': ' + msg);
    e.prolog = true; e.pos = pos; e.line = line; return e;
  }
  function tokenize(src) {
    const toks = []; let i = 0; const n = src.length;
    let layoutBefore = true;
    while (i < n) {
      const c = src[i];
      if (/\s/.test(c)) { i++; layoutBefore = true; continue; }
      if (c === '%') { while (i < n && src[i] !== '\n') i++; layoutBefore = true; continue; }
      if (c === '/' && src[i + 1] === '*') { const j = src.indexOf('*/', i + 2); if (j < 0) throw PrologSyntaxError('unterminated block comment', i, src); i = j + 2; layoutBefore = true; continue; }
      const start = i; const lb = layoutBefore; layoutBefore = false;
      if (/[0-9]/.test(c)) {
        if (c === '0' && src[i + 1] === "'") {
          i += 2; let ch = src[i];
          if (ch === '\\') { const r = readEscape(src, i + 1); toks.push({ k: 'num', v: r.ch.codePointAt(0), pos: start, lb }); i = r.i; continue; }
          if (ch === "'" && src[i + 1] === "'") { toks.push({ k: 'num', v: 39, pos: start, lb }); i += 2; continue; }
          const cp = src.codePointAt(i); toks.push({ k: 'num', v: cp, pos: start, lb }); i += cp > 0xffff ? 2 : 1; continue;
        }
        if (c === '0' && /[xob]/.test(src[i + 1] || '') ) {
          const base = { x: 16, o: 8, b: 2 }[src[i + 1]]; const re = base === 16 ? /[0-9a-fA-F]/ : base === 8 ? /[0-7]/ : /[01]/;
          let j = i + 2; while (j < n && re.test(src[j])) j++;
          if (j > i + 2) { toks.push({ k: 'num', v: bigOrNum(BigInt((base === 16 ? '0x' : base === 8 ? '0o' : '0b') + src.slice(i + 2, j))), pos: start, lb }); i = j; continue; }
        }
        let j = i; while (j < n && /[0-9_]/.test(src[j])) j++;
        let isF = false;
        if (src[j] === '.' && /[0-9]/.test(src[j + 1] || '')) { isF = true; j++; while (j < n && /[0-9]/.test(src[j])) j++; }
        if ((src[j] === 'e' || src[j] === 'E') && /[0-9+-]/.test(src[j + 1] || '')) {
          let k = j + 1; if (src[k] === '+' || src[k] === '-') k++;
          if (/[0-9]/.test(src[k] || '')) { isF = true; j = k; while (j < n && /[0-9]/.test(src[j])) j++; }
        }
        const text = src.slice(i, j).replace(/_/g, '');
        toks.push({ k: 'num', v: isF ? parseFloat(text) : bigOrNum(BigInt(text)), f: isF, pos: start, lb }); i = j; continue;
      }
      if (c === '_' || /[A-Z]/.test(c) || c > '\x7f' && /\p{Lu}|\p{Lt}/u.test(c)) { let j = i; while (j < n && isAlnum(src[j])) j++; toks.push({ k: 'var', v: src.slice(i, j), pos: start, lb }); i = j; continue; }
      if (/[a-z]/.test(c) || c > '\x7f' && /[\p{Ll}\p{Lo}\p{Lm}]/u.test(c)) { let j = i; while (j < n && isAlnum(src[j])) j++; toks.push({ k: 'atom', v: src.slice(i, j), pos: start, lb }); i = j; continue; }
      if (c === "'" || c === '"' || c === '`') {
        const q = c; let j = i + 1; let s = '';
        for (;;) {
          if (j >= n) throw PrologSyntaxError('unterminated quoted', i, src);
          const d = src[j];
          if (d === q) { if (src[j + 1] === q) { s += q; j += 2; continue; } j++; break; }
          if (d === '\\') {
            if (src[j + 1] === '\n') { j += 2; continue; }
            const r = readEscape(src, j + 1); s += r.ch; j = r.i; continue;
          }
          s += d; j++;
        }
        toks.push({ k: q === "'" ? 'qatom' : q === '"' ? 'str' : 'bq', v: s, pos: start, lb }); i = j; continue;
      }
      if (c === '(' || c === ')' || c === '[' || c === ']' || c === '{' || c === '}' || c === ',' || c === '|') {
        if (c === '|' && src[i + 1] === '|') { toks.push({ k: 'atom', v: '||', pos: start, lb }); i += 2; continue; }
        toks.push({ k: 'punct', v: c, pos: start, lb }); i++; continue;
      }
      if (c === '!' || c === ';') { toks.push({ k: 'atom', v: c, pos: start, lb }); i++; continue; }
      if (isSym(c)) {
        let j = i; while (j < n && isSym(src[j])) j++;
        const text = src.slice(i, j);
        if (text === '.' && (j >= n || /\s|%/.test(src[j]))) { toks.push({ k: 'end', pos: start, lb }); i = j; continue; }
        toks.push({ k: 'atom', v: text, pos: start, lb }); i = j; continue;
      }
      throw PrologSyntaxError('unexpected character ' + JSON.stringify(c), i, src);
    }
    toks.push({ k: 'eof', pos: n });
    return toks;
  }
  function readEscape(src, i) {
    const c = src[i];
    const simple = { n: '\n', t: '\t', r: '\r', a: '\x07', b: '\b', f: '\f', v: '\v', '0': '\0', '\\': '\\', "'": "'", '"': '"', '`': '`', e: '\x1b', s: ' ' };
    if (c === 'x') { let j = i + 1; let h = ''; while (/[0-9a-fA-F]/.test(src[j])) h += src[j++]; if (src[j] === '\\') j++; return { ch: String.fromCodePoint(parseInt(h, 16)), i: j }; }
    if (/[0-7]/.test(c)) { let j = i; let o = ''; while (/[0-7]/.test(src[j])) o += src[j++]; if (src[j] === '\\') j++; return { ch: String.fromCodePoint(parseInt(o, 8)), i: j }; }
    if (c in simple) return { ch: simple[c], i: i + 1 };
    return { ch: c, i: i + 1 };
  }

  // ---------- parser ----------
  function Parser(src) { this.src = src; this.toks = tokenize(src); this.i = 0; this.varMap = null; this.varNames = null; }
  Parser.prototype.peek = function () { return this.toks[this.i]; };
  Parser.prototype.next = function () { return this.toks[this.i++]; };
  Parser.prototype.err = function (msg, tok) { throw PrologSyntaxError(msg, (tok || this.peek()).pos, this.src); };
  Parser.prototype.expect = function (k, v) { const t = this.next(); if (t.k !== k || (v !== undefined && t.v !== v)) this.err('expected ' + (v || k), t); return t; };
  Parser.prototype.readClause = function () {
    if (this.peek().k === 'eof') return null;
    this.varMap = new Map(); this.varNames = [];
    const t = this.parse(1200);
    this.expect('end');
    return { term: t, vars: this.varNames.slice() };
  };
  Parser.prototype.mkVar = function (nm) {
    if (nm === '_') return Var('_');
    let v = this.varMap.get(nm); if (!v) { v = Var(nm); this.varMap.set(nm, v); this.varNames.push([nm, v]); }
    return v;
  };
  function isTermStart(tok) {
    if (!tok) return false;
    if (tok.k === 'eof' || tok.k === 'end') return false;
    if (tok.k === 'punct') return tok.v === '(' || tok.v === '[' || tok.v === '{';
    if (tok.k === 'atom' && ops.infix.has(tok.v) && !ops.prefix.has(tok.v)) return false;
    return true;
  }
  Parser.prototype.parsePrimary = function (maxPrec) {
    const tok = this.next();
    switch (tok.k) {
      case 'num': return { term: Num(tok.v, tok.f), prec: 0 };
      case 'var': { const v = this.mkVar(tok.v); const p = this.peek(); if (p.k === 'punct' && p.v === '{' && !p.lb) return { term: this.parseDict(v), prec: 0 }; return { term: v, prec: 0 }; }
      case 'str': return { term: Str(tok.v), prec: 0 };
      case 'bq': return { term: list([...tok.v].map(ch => Int(ch.codePointAt(0)))), prec: 0 };
      case 'punct':
        if (tok.v === '(') { const t = this.parse(1200); this.expect('punct', ')'); return { term: t, prec: 0 }; }
        if (tok.v === '[') {
          if (this.peek().k === 'punct' && this.peek().v === ']') { this.next(); return this.afterAtom('[]', tok, maxPrec); }
          const items = [this.parse(999)]; let tail = NIL;
          for (;;) {
            const p = this.peek();
            if (p.k === 'punct' && p.v === ',') { this.next(); items.push(this.parse(999)); continue; }
            if (p.k === 'punct' && p.v === '|') { this.next(); tail = this.parse(999); }
            break;
          }
          this.expect('punct', ']');
          return { term: list(items, tail), prec: 0 };
        }
        if (tok.v === '{') {
          if (this.peek().k === 'punct' && this.peek().v === '}') { this.next(); return this.afterAtom('{}', tok, maxPrec); }
          const t = this.parse(1200); this.expect('punct', '}'); return { term: Cmp('{}', [t]), prec: 0 };
        }
        if (tok.v === ',') this.err('unexpected comma', tok);
        if (tok.v === '|') return this.afterAtom('|', tok, maxPrec);
        this.err('unexpected ' + tok.v, tok);
        break;
      case 'atom': case 'qatom': return this.afterAtom(tok.v, tok, maxPrec);
      case 'end': this.err('unexpected end of clause', tok); break;
      default: this.err('unexpected end of input', tok);
    }
  };
  // SWI-Prolog dicts: Tag{Key: Value, ...} with no space before {, as dict(Tag, [Key-Value, ...]) with the
  // pairs in standard order of keys
  Parser.prototype.parseDict = function (tag) {
    this.next(); const pairs = [];
    if (!(this.peek().k === 'punct' && this.peek().v === '}')) {
      for (;;) {
        const kv = deref(this.parse(999));
        if (!(kv.t === 'c' && kv.f === ':' && kv.a.length === 2)) this.err('dict pairs are Key:Value', this.peek());
        pairs.push([deref(kv.a[0]), kv.a[1]]);
        if (this.peek().k === 'punct' && this.peek().v === ',') { this.next(); continue; }
        break;
      }
    }
    this.expect('punct', '}');
    return mkDict(tag, pairs);
  };
  Parser.prototype.afterAtom = function (nm, tok, maxPrec) {
    const p = this.peek();
    if ((tok.k === 'atom' && /^[a-z]/.test(nm) || tok.k === 'qatom') && p.k === 'punct' && p.v === '{' && !p.lb) return { term: this.parseDict(Atom(nm)), prec: 0 };
    if (p.k === 'punct' && p.v === '(' && !p.lb) {
      this.next(); const a = [this.parse(999)];
      while (this.peek().k === 'punct' && this.peek().v === ',') { this.next(); a.push(this.parse(999)); }
      this.expect('punct', ')');
      return { term: Cmp(nm, a), prec: 0 };
    }
    if (tok.k === 'atom' && nm === '-' && p.k === 'num' && !p.lb) { this.next(); return { term: Num(-p.v, p.f), prec: 0 }; }
    if (tok.k === 'atom' && ops.prefix.has(nm)) {
      const op = ops.prefix.get(nm);
      const nx = this.peek();
      let operand = isTermStart(nx);
      // an infix-operator name written as a functor (-div(X, Y), -mod(A, B)) starts an operand
      const nxFunctor = nx && nx.k === 'atom' && this.toks[this.i + 1] && this.toks[this.i + 1].k === 'punct' && this.toks[this.i + 1].v === '(' && !this.toks[this.i + 1].lb;
      if (nxFunctor) operand = true;
      if (operand && nx.k === 'atom' && ops.infix.has(nx.v)) {
        // `- = x` : prefix op followed by an infix op -> treat as atom, unless the infix atom is a term itself (f( or prefix op)
        const n2 = this.toks[this.i + 1];
        const isFunctor = n2 && n2.k === 'punct' && n2.v === '(' && !n2.lb;
        if (!isFunctor && !ops.prefix.has(nx.v)) operand = false;
      }
      if (operand) {
        let p2 = op.p; if (p2 > maxPrec) p2 = 999;
        const argMax = op.type === 'fy' ? p2 : p2 - 1;
        const save = this.i;
        try { const arg = this.parse(argMax); return { term: Cmp(nm, [arg]), prec: p2 }; }
        catch (e) { this.i = save; }
      }
      return { term: Atom(nm), prec: op.p > maxPrec ? 0 : op.p };
    }
    let pr = (ops.infix.has(nm) || ops.prefix.has(nm)) ? Math.max(ops.infix.has(nm) ? ops.infix.get(nm).p : 0, 0) : 0;
    // an operator atom used as an operand (is/2, (dynamic)/1) is an ordinary atom, as in SWI-Prolog
    const nx = this.peek();
    if (pr && nx && (nx.k === 'atom' && ops.infix.has(nx.v) || nx.k === 'punct' && (nx.v === ',' || nx.v === '|' || nx.v === ')' || nx.v === ']' || nx.v === '}'))) pr = 0;
    return { term: Atom(nm), prec: pr > maxPrec ? 0 : pr };
  };
  Parser.prototype.parse = function (maxPrec) {
    let { term: left, prec: leftPrec } = this.parsePrimary(maxPrec);
    for (;;) {
      const tok = this.peek();
      let nm = null;
      if (tok.k === 'atom') nm = tok.v;
      else if (tok.k === 'punct' && (tok.v === ',' || tok.v === '|')) nm = tok.v;
      else break;
      const op = ops.infix.get(nm);
      if (op) {
        const p = op.p;
        const la = op.type[0] === 'y' ? p : p - 1;
        const ra = op.type[2] === 'y' ? p : p - 1;
        if (p <= maxPrec && leftPrec <= la) {
          this.next();
          const right = this.parse(ra);
          // SWI-Prolog's dict access: Dict.key, Dict.put(...) (expanded where the clause is added)
          if (nm === '.' && !tok.lb) { left = Cmp('$dot', [left, right]); leftPrec = 0; continue; }
          const f = nm === '|' ? ';' : nm;
          left = Cmp(f, [left, right]); leftPrec = p; continue;
        }
      }
      const pop = ops.postfix.get(nm);
      if (pop && pop.p <= maxPrec) { this.next(); left = Cmp(nm, [left]); leftPrec = pop.p; continue; }
      break;
    }
    return left;
  };

  // :- op(P, T, Names) and the op(P, T, Names) a module exports change how what follows is read
  function applyOpDirective(d) {
    d = deref(d);
    if (d.t === 'c' && d.f === 'op' && d.a.length === 3) {
      const pr = deref(d.a[0]).v, ty = deref(d.a[1]).n; const nmT = deref(d.a[2]);
      const names = listToArray(nmT) || [nmT];
      names.forEach(x => { x = deref(x); if (x.t === 'c' && x.f === ':' && x.a.length === 2) x = deref(x.a[1]); if (x.t === 'a') addOp(pr, ty, x.n); });
    }
    if (d.t === 'c' && d.f === 'module' && d.a.length === 2) for (const x of listToArray(d.a[1]) || []) applyOpDirective(x);
  }
  function readProgram(src) {
    const p = new Parser(src); const out = [];
    for (;;) {
      const c = p.readClause(); if (!c) break;
      const t = c.term;
      if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
        const d = deref(t.a[0]);
        applyOpDirective(d);
      }
      out.push(c);
    }
    return out;
  }
  function readTerm(src) {
    const s = src.trim().replace(/\.\s*$/, '');
    const p = new Parser(s + ' .'); const c = p.readClause(); if (!c) throw PrologSyntaxError('empty term', 0, src);
    return c;
  }

  // ---------- printer ----------
  function atomNeedsQuote(n) {
    if (n === '[]' || n === '!' || n === ';' || n === '{}' || n === ',') return n === ',';
    if (/^[a-z][A-Za-z0-9_]*$/.test(n)) return false;
    if (/^[+\-*/\\^<>=~:.?@#&$]+$/.test(n)) return false;
    if (/^[\p{Ll}\p{Lo}\p{Lm}][\p{L}\p{N}_]*$/u.test(n)) return false;
    if (n.length && [...n].every((c) => isSym(c))) return false;
    return true;
  }
  function quoteAtom(n) {
    return "'" + n.replace(/\\/g, '\\\\').replace(/'/g, "\\'").replace(/\n/g, '\\n').replace(/\t/g, '\\t') + "'";
  }
  function fmtAtom(n, q) { return q && atomNeedsQuote(n) ? quoteAtom(n) : n; }
  function bigOrNum(b) { return b >= -9007199254740991n && b <= 9007199254740991n ? Number(b) : b; }
  function fmtNum(t) {
    if (t.f) { let s = String(t.v); if (!/[.eE]/.test(s) && isFinite(t.v)) s += '.0'; if (s === 'Infinity') s = 'inf'; if (s === '-Infinity') s = '-inf'; if (s === 'NaN') s = 'nan'; return s; }
    return String(t.v);
  }
  // opts: {quoted, varName: fn(v)->string, ignoreOps}
  function show(t, opts) {
    opts = opts || {};
    const q = opts.quoted !== false;
    const vn0 = v => v.name && v.name !== '_' ? v.name : '_G' + v.id;
    // swi: as SWI-Prolog's write/print/writeq lay terms out (no space after commas, none around
    // symbolic operators); without it, as its toplevel shows answers
    const swi = !!opts.swi, sep = swi && !opts.nextArg ? ',' : ', ';
    // SWI-Prolog writes a variable as _N, never by its name in the source (two copies of a clause
    // must not print the same name)
    const vn = opts.varName || (swi ? (v => '_G' + v.id) : vn0);
    function w(t, maxP, operand = false) {
      t = deref(t);
      switch (t.t) {
        case 'v': return vn(t);
        case 'n': { const s = fmtNum(t); return s; }
        case 's': return q ? JSON.stringify(t.v) : t.v;
        case 'a': { const s = fmtAtom(t.n, q); const isOp = ops.infix.has(t.n) || ops.prefix.has(t.n) || ops.postfix.has(t.n) || t.n === ';' || t.n === '|'; if (isOp && t.n !== '[]' && t.n !== '{}' && t.n !== '!') { if (operand) return '(' + s + ')'; const p = Math.max(ops.infix.has(t.n) ? ops.infix.get(t.n).p : 0, ops.prefix.has(t.n) ? ops.prefix.get(t.n).p : 0, t.n === ';' || t.n === '|' ? 1100 : 0); if (p > maxP) return '(' + s + ')'; } return s; }
        case 'c': {
          if (t.f === '$VAR' && t.a.length === 1 && opts.numbervars !== false) { const n = deref(t.a[0]); if (n.t === 'n' && !n.f && n.v >= 0) return String.fromCharCode(65 + n.v % 26) + (n.v >= 26 ? Math.floor(n.v / 26) : ''); if (n.t === 'a') return n.n; if (n.t === 's') return n.v; }
          if (t.f === 'dict' && t.a.length === 2) { const ps = dictPairs(t); if (ps) { const tg = deref(t.a[0]); return (tg.t === 'v' ? '_' : w(tg, 0)) + '{' + ps.map(([k, v]) => w(k, 0) + ':' + w(v, 599)).join(sep) + '}'; } }
          if (t.f === '.' && t.a.length === 2) {
            const items = []; let x = t;
            while (x.t === 'c' && x.f === '.' && x.a.length === 2) { items.push(w(x.a[0], 999)); x = deref(x.a[1]); }
            let s = '[' + items.join(sep);
            if (!(x.t === 'a' && x.n === '[]')) s += '|' + w(x, 999);
            return s + ']';
          }
          if (t.f === '{}' && t.a.length === 1) return '{' + w(t.a[0], 1200) + '}';
          if (!opts.ignoreOps && t.a.length === 2 && ops.infix.has(t.f) && t.f !== '|') { // '|'(A, B) is written as a compound
            const op = ops.infix.get(t.f); const p = op.p;
            const lp = op.type[0] === 'y' ? p : p - 1, rp = op.type[2] === 'y' ? p : p - 1;
            // an operator atom as an operand is bracketed: (is) = (-), \+ (;)
            let l = w(t.a[0], lp, true), r = w(t.a[1], rp, true);
            let s;
            if (t.f === ',') s = l + sep + r;
            else if (swi && !/^[a-z]/.test(t.f)) { const ft = fmtAtom(t.f, q); const glueR = isSym(ft[ft.length - 1]) && (isSym(r[0]) || /^-?\d/.test(r) && r[0] === '-'); const glueL = isSym(ft[0]) && isSym(l[l.length - 1]); s = l + (glueL ? ' ' : '') + ft + (glueR ? ' ' : '') + r; }
            else if (/^[a-z]/.test(t.f) || ['->', ':-', '-->', ';', '*->', 'is', '=', '\\=', '==', '\\==', '=..', '<', '>', '=<', '>=', '=:=', '=\\=', '@<', '@>', '@=<', '@>='].includes(t.f) || p >= 700) s = l + ' ' + fmtAtom(t.f, q) + ' ' + r;
            else {
              // avoid gluing symbol chars, e.g. 1- -1, a- (-b)
              const ft = fmtAtom(t.f, q);
              const glueR = isSym(ft[ft.length - 1]) && (isSym(r[0]) || /^-?\d/.test(r) && r[0] === '-');
              const glueL = isSym(ft[0]) && isSym(l[l.length - 1]);
              s = l + (glueL ? ' ' : '') + ft + (glueR ? ' ' : '') + r;
            }
            return p > maxP ? '(' + s + ')' : s;
          }
          if (!opts.ignoreOps && t.a.length === 1 && ops.prefix.has(t.f) && t.f !== '-' && t.f !== '+' || (!opts.ignoreOps && t.a.length === 1 && (t.f === '-' || t.f === '+'))) {
            const op = ops.prefix.get(t.f);
            if (op) {
              const p = op.p; const ap = op.type === 'fy' ? p : p - 1;
              const a0 = deref(t.a[0]);
              // a prefix operator term or an operator atom as the operand is bracketed: -(+a), \+ (is)
              const a0op = a0.t === 'c' && a0.a.length === 1 && ops.prefix.has(a0.f) && !(a0.f === '-' || a0.f === '+') ? false : a0.t === 'c' && a0.a.length <= 2 && (a0.a.length === 1 ? ops.prefix.has(a0.f) : false);
              let as = a0op ? '(' + w(a0, 1200) + ')' : w(a0, ap, true);
              const ft = fmtAtom(t.f, q);
              const needSpace = /^[a-z]/i.test(ft) || !swi && ft === '\\+' || isSym(ft[ft.length - 1]) && (isSym(as[0]) || a0.t === 'n') || as[0] === '(';
              const s = ft + (needSpace ? ' ' : '') + as;
              return p > maxP ? '(' + s + ')' : s;
            }
          }
          return fmtAtom(t.f, q) + '(' + t.a.map(x => w(x, 999)).join(sep) + ')';
        }
      }
      return '?';
    }
    return w(t, opts.prec || 1200);
  }
  // names variables of a term _A,_B.. (or by provided names) for output
  function namer(namesMap) {
    const m = new Map(); let k = 0;
    return v => {
      if (namesMap && namesMap.has(v)) return namesMap.get(v);
      let s = m.get(v);
      if (!s) { s = '_' + letters(k++); m.set(v, s); }
      return s;
    };
  }
  function letters(k) { let s = ''; do { s = String.fromCharCode(65 + (k % 26)) + s; k = Math.floor(k / 26) - 1; } while (k >= 0); return s; }

  // pretty-print a clause with indentation of control constructs
  function showClause(cl, opts) {
    opts = opts || {};
    const vn = opts.varName || namer();
    const o = { varName: vn, quoted: true };
    cl = deref(cl);
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 2) {
      const body = deref(cl.a[1]);
      if (body.t === 'a' && body.n === 'true') return show(cl.a[0], Object.assign({ prec: 1199 }, o)) + '.';
      return show(cl.a[0], Object.assign({ prec: 1199 }, o)) + ' :-\n' + showBody(body, 1, o) + '.';
    }
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 1) return ':- ' + show(cl.a[0], Object.assign({ prec: 1199 }, o)) + '.';
    return show(cl, Object.assign({ prec: 1199 }, o)) + '.';
  }
  function showBody(b, d, o) {
    const ind = '    '.repeat(d);
    b = deref(b);
    if (b.t === 'c' && b.f === ',' && b.a.length === 2) return showBody(b.a[0], d, o) + ',\n' + showBody(b.a[1], d, o);
    if (b.t === 'c' && (b.f === ';' || b.f === '->' || b.f === '*->') && b.a.length === 2) {
      return ind + '(   ' + showDisj(b, d, o).replace(/^\s+/, '') + '\n' + ind + ')';
    }
    if (b.t === 'c' && b.f === 'if_commit' && b.a.length === 3 && o.layoutIfCommit !== false) {
      const inner = '    '.repeat(d + 1);
      return ind + 'if_commit(\n' + showGoalBlock(b.a[0], d + 1, o) + ',\n' + showGoalBlock(b.a[1], d + 1, o) + ',\n' + showGoalBlock(b.a[2], d + 1, o) + '\n' + ind + ')';
    }
    return ind + show(b, Object.assign({ prec: 999 }, o));
  }
  function showGoalBlock(g, d, o) {
    g = deref(g);
    if (g.t === 'c' && g.f === ',' && g.a.length === 2) {
      const ind = '    '.repeat(d);
      return ind + '(\n' + showBody(g, d + 1, o) + '\n' + ind + ')';
    }
    return showBody(g, d, o);
  }
  function showDisj(b, d, o) {
    const ind = '    '.repeat(d);
    b = deref(b);
    if (b.t === 'c' && b.f === ';' && b.a.length === 2) {
      return showDisj(b.a[0], d, o) + '\n' + ind + ';   ' + showDisj(b.a[1], d, o).replace(/^\s+/, '');
    }
    if (b.t === 'c' && (b.f === '->' || b.f === '*->') && b.a.length === 2) {
      return showBody(b.a[0], d + 1, o).replace(/^\s+/, '') + '\n' + ind + b.f + '  ' + showBody(b.a[1], d + 1, o).replace(/^\s+/, '');
    }
    return showBody(b, d + 1, o).replace(/^\s+/, '');
  }

  P.varCount = () => varCounter;
  Object.assign(P, { mkDict, dictPairs, applyOpDirective,
    Atom, Num, Int, Str, Var, Cmp, NIL, TRUE, FAIL, cons, list, deref, isCons, isNil, listToArray,
    name, arity, key, args, copy, resolve, termVars, isGround, compare, variantKey,
    ops, addOp, tokenize, Parser, readProgram, readTerm, show, showClause, namer, letters, PrologSyntaxError,
    atomNeedsQuote, fmtAtom
  });
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog reference engine: ordinary Prolog semantics (cut, backtracking) with
   step / choicepoint counting.  It is the oracle that every conversion is checked against. */
(function (P) {
  'use strict';
  const { Atom, Num, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, isNil, listToArray, copy, termVars, isGround, compare, show } = P;

  function PlError(term) { this.term = term; this.prolog = true; this.message = 'Prolog error: ' + show(term); }
  PlError.prototype = Object.create(Error.prototype);
  function typeError(type, culprit) { return new PlError(Cmp('error', [Cmp('type_error', [Atom(type), culprit]), Var()])); }
  function instErr() { return new PlError(Cmp('error', [Atom('instantiation_error'), Var()])); }
  function existErr(k) { const [n, a] = splitKey(k); return new PlError(Cmp('error', [Cmp('existence_error', [Atom('procedure'), Cmp('/', [Atom(n), Int(+a)])]), Var()])); }
  function evalErr(e) { return new PlError(Cmp('error', [Cmp('evaluation_error', [Atom(e)]), Var()])); }
  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }
  class LimitError extends Error { constructor(m) { super(m); this.limit = true; } }

  // ---------- program ----------
  function Program() { this.preds = new Map(); this.order = []; this.dynamic = new Set(); this.directives = []; this.clauses = []; }
  Program.prototype.add = function (term, vars, atEnd) {
    term = deref(term);
    if (P.expandDots && P.hasDots(term)) term = P.expandDots(term);
    let head = term, body = P.TRUE;
    if (term.t === 'c' && term.f === ':-' && term.a.length === 2) { head = deref(term.a[0]); body = term.a[1]; }
    else if (term.t === 'c' && term.f === ':-' && term.a.length === 1) { this.directives.push(term.a[0]); return; }
    else if (term.t === 'c' && term.f === '-->' && term.a.length === 2) { const t = dcgTransform(term); return this.add(t, vars, atEnd); }
    // Module:Head defines Head (modules are flat here; src/swi.js renames private predicates)
    while (head.t === 'c' && head.f === ':' && head.a.length === 2 && deref(head.a[0]).t === 'a') head = deref(head.a[1]);
    if (head.t === 'v') throw new Error('clause head is a variable');
    if (head.t !== 'a' && head.t !== 'c') throw new Error('clause head is not callable: ' + show(head));
    const k = P.key(head);
    if (!this.preds.has(k)) { this.preds.set(k, []); this.order.push(k); }
    const cl = { head, body, vars: vars || null, nvars: termVars(Cmp('-', [head, body])).length };
    if (atEnd === false) this.preds.get(k).unshift(cl); else this.preds.get(k).push(cl);
    this.clauses.push(cl);
    return cl;
  };
  function loadProgram(src) {
    const prog = new Program();
    const cls = typeof src === 'string' ? P.readProgram(src) : src;
    for (const c of cls) {
      const t = deref(c.term);
      if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
        const d = deref(t.a[0]);
        if (d.t === 'c' && d.f === 'dynamic') { for (const s of commaList(d.a[0])) { const sd = deref(s); if (sd.t === 'c' && sd.f === '/') { const k = P.name(sd.a[0]) + '/' + deref(sd.a[1]).v; prog.dynamic.add(k); if (!prog.preds.has(k)) { prog.preds.set(k, []); prog.order.push(k); } } } }
        prog.directives.push(d);
        continue;
      }
      prog.add(t, c.vars);
    }
    return prog;
  }
  function commaList(t) { t = deref(t); const out = []; while (t.t === 'c' && t.f === ',' && t.a.length === 2) { out.push(t.a[0]); t = deref(t.a[1]); } const l = listToArray(t); if (l) return out.concat(l); out.push(t); return out; }

  // DCG translation
  function dcgTransform(rule) {
    const head = deref(rule.a[0]), body = rule.a[1];
    const S0 = Var('S0'), S = Var('S');
    let pushback = null, h = head;
    if (h.t === 'c' && h.f === ',' ) { pushback = h.a[1]; h = deref(h.a[0]); }
    const nh = addArgs(h, S0, S);
    if (pushback) { const M = Var(); return Cmp(':-', [nh, Cmp(',', [dcgBody(body, S0, M), terminals(pushback, S, M)])]); }
    return Cmp(':-', [nh, dcgBody(body, S0, S)]);
  }
  function addArgs(t, a, b) { t = deref(t); if (t.t === 'a') return Cmp(t.n, [a, b]); if (t.t === 'c') return Cmp(t.f, t.a.concat([a, b])); throw new Error('bad DCG head'); }
  function terminals(lst, S0, S) { const arr = listToArray(lst); return Cmp('=', [S0, list(arr, S)]); }
  function dcgBody(b, S0, S) {
    b = deref(b);
    if (b.t === 'v') return Cmp('phrase', [b, S0, S]);
    if (b.t === 'c' && b.f === ',' && b.a.length === 2) { const M = Var(); return Cmp(',', [dcgBody(b.a[0], S0, M), dcgBody(b.a[1], M, S)]); }
    if (b.t === 'c' && (b.f === ';' || b.f === '|') && b.a.length === 2) return Cmp(';', [dcgBody(b.a[0], S0, S), dcgBody(b.a[1], S0, S)]);
    if (b.t === 'c' && b.f === '->' && b.a.length === 2) { const M = Var(); return Cmp('->', [dcgBody(b.a[0], S0, M), dcgBody(b.a[1], M, S)]); }
    if (b.t === 'c' && b.f === '\\+' && b.a.length === 1) return Cmp(',', [Cmp('\\+', [dcgBody(b.a[0], S0, Var())]), Cmp('=', [S0, S])]);
    if (b.t === 'a' && b.n === '!') return Cmp(',', [Atom('!'), Cmp('=', [S0, S])]);
    if (b.t === 'a' && b.n === '[]') return Cmp('=', [S0, S]);
    if (b.t === 'c' && b.f === '{}' && b.a.length === 1) return Cmp(',', [b.a[0], Cmp('=', [S0, S])]);
    if (isCons(b)) return terminals(b, S0, S);
    if (b.t === 's') return terminals(list([...b.v].map(c => Int(c.codePointAt(0)))), S0, S);
    if (b.t === 'c' && b.f === 'call') return Cmp('call', b.a.concat([S0, S]));
    return addArgs(b, S0, S);
  }

  // ---------- arithmetic ----------
  function evalArith(t) {
    t = deref(t);
    switch (t.t) {
      case 'n': return t;
      case 'v': throw instErr();
      case 's': if (t.v.length === 1) return Int(t.v.codePointAt(0)); throw typeError('evaluable', t);
      case 'a': {
        switch (t.n) {
          case 'pi': return Num(Math.PI, true); case 'e': return Num(Math.E, true);
          case 'inf': case 'infinite': return Num(Infinity, true); case 'nan': return Num(NaN, true);
          case 'max_tagged_integer': return Int(Number.MAX_SAFE_INTEGER); case 'epsilon': return Num(Number.EPSILON, true);
          case 'random': return Num(Math.random(), true); case 'random_float': return Num(Math.random(), true);
          case 'cputime': return Num(now() / 1000, true); case 'realtime': return Int(Math.floor(Date.now() / 1000));
          case '[]': break;
        }
        throw typeError('evaluable', Cmp('/', [t, Int(0)]));
      }
      case 'c': {
        if (t.f === '.' && t.a.length === 2 && isNil(deref(t.a[1]))) return evalArith(t.a[0]);
        const xs = t.a.map(evalArith);
        const a = xs[0], b = xs[1];
        const fl = xs.some(x => x.f);
        // integers are unbounded (BigInt beyond the safe range); fa, fb: the values as JS numbers, for floats
        const fa = a && typeof a.v === 'bigint' ? Number(a.v) : a && a.v, fb = b && typeof b.v === 'bigint' ? Number(b.v) : b && b.v;
        const big = x => BigInt(x.v);
        // an exact integer result: JS numbers while the result is safe, BigInt otherwise
        const iop = (f, g) => { if (typeof a.v === 'number' && (!b || typeof b.v === 'number')) { const r = f(a.v, b && b.v); if (Number.isSafeInteger(r)) return Int(r); } return Int(g(big(a), b && big(b))); };
        const needInt = () => { for (const x of xs) if (x.f) throw typeError('integer', x); };
        const isZero = x => x.v === 0 || x.v === 0n;
        const small = typeof a.v === 'number' && b && typeof b.v === 'number';
        const neg = x => x.v < 0;
        if (t.a.length === 1) switch (t.f) {
          case '-': return a.f ? Num(-a.v, true) : Int(-a.v);
          case '+': return a;
          case 'abs': return a.f ? Num(Math.abs(a.v), true) : neg(a) ? Int(-a.v) : a;
          case 'sign': return a.f ? Num(Math.sign(a.v), true) : Int(neg(a) ? -1 : isZero(a) ? 0 : 1);
          case 'min': case 'max': break;
          case 'sqrt': return Num(Math.sqrt(fa), true);
          case 'sin': return Num(Math.sin(fa), true); case 'cos': return Num(Math.cos(fa), true); case 'tan': return Num(Math.tan(fa), true);
          case 'asin': return Num(Math.asin(fa), true); case 'acos': return Num(Math.acos(fa), true); case 'atan': return Num(Math.atan(fa), true);
          case 'exp': return Num(Math.exp(fa), true);
          case 'log': if (fa <= 0) throw evalErr('undefined'); return Num(Math.log(fa), true);
          case 'log2': return Num(Math.log2(fa), true);
          case 'float': return Num(fa, true);
          case 'integer': return a.f ? Int(roundBig(a.v)) : a;
          case 'float_integer_part': return Num(Math.trunc(fa), true);
          case 'float_fractional_part': return Num(fa - Math.trunc(fa), true);
          case 'truncate': return a.f ? Int(toBig(Math.trunc(a.v))) : a;
          case 'round': return a.f ? Int(roundBig(a.v)) : a;
          case 'ceiling': return a.f ? Int(toBig(Math.ceil(a.v))) : a;
          case 'floor': return a.f ? Int(toBig(Math.floor(a.v))) : a;
          case '\\': needInt(); return Int(~big(a));
          case 'msb': needInt(); return Int(big(a).toString(2).length - 1);
          case 'succ': needInt(); return iop(x => x + 1, x => x + 1n);
          case 'random': needInt(); return Int(Math.floor(Math.random() * fa));
          case 'random_float': return Num(Math.random(), true);
        }
        if (t.a.length === 2) switch (t.f) {
          case '+': return fl ? Num(fa + fb, true) : iop((x, y) => x + y, (x, y) => x + y);
          case '-': return fl ? Num(fa - fb, true) : iop((x, y) => x - y, (x, y) => x - y);
          case '*': return fl ? Num(fa * fb, true) : iop((x, y) => x * y, (x, y) => x * y);
          case '/': if (isZero(b) && !fl) throw evalErr('zero_divisor'); if (!fl) { if (small) return a.v % b.v === 0 ? Int(a.v / b.v) : Num(a.v / b.v, true); if (big(a) % big(b) === 0n) return Int(big(a) / big(b)); return Num(fa / fb, true); } if (fb === 0) throw evalErr('zero_divisor'); return Num(fa / fb, true);
          case '//': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); return iop((x, y) => Math.trunc(x / y), (x, y) => x / y);
          case 'div': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); return small ? Int(Math.floor(a.v / b.v)) : Int(floorDiv(big(a), big(b)));
          case 'mod': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); if (small) { const m = a.v % b.v; return Int(m !== 0 && (m < 0) !== (b.v < 0) ? m + b.v : m); } { const m = big(a) % big(b); return Int(m !== 0n && (m < 0n) !== (big(b) < 0n) ? m + big(b) : m); }
          case 'rem': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); return small ? Int(a.v % b.v) : Int(big(a) % big(b));
          case 'min': return compareNum(a, b) <= 0 ? a : b;
          case 'max': return compareNum(a, b) >= 0 ? a : b;
          case '**': if (!fl && !neg(b)) return Int(big(a) ** big(b)); return Num(Math.pow(fa, fb), true);
          case '^': if (!fl) { if (neg(b)) { if (a.v === 1) return Int(1); if (a.v === -1) return Int(big(b) % 2n ? -1 : 1); throw evalErr('undefined'); } return Int(big(a) ** big(b)); } return Num(Math.pow(fa, fb), true);
          case 'atan2': case 'atan': return Num(Math.atan2(fa, fb), true);
          case 'log': return Num(Math.log(fb) / Math.log(fa), true);
          case '>>': needInt(); return Int(big(a) >> big(b));
          case '<<': needInt(); return Int(big(a) << big(b));
          case '/\\': needInt(); return Int(big(a) & big(b));
          case '\\/': needInt(); return Int(big(a) | big(b));
          case 'xor': needInt(); return Int(big(a) ^ big(b));
          case 'gcd': { needInt(); let x = big(a), y = big(b); if (x < 0n) x = -x; if (y < 0n) y = -y; while (y) { [x, y] = [y, x % y]; } return Int(x); }
          case 'copysign': return Num(Math.sign(fb) * Math.abs(fa), true);
          case 'truncate': break;
          case 'cot': break;
          case 'random_between': break;
        }
        throw typeError('evaluable', Cmp('/', [Atom(t.f), Int(t.a.length)]));
      }
    }
    throw typeError('evaluable', t);
  }
  function compareNum(a, b) { return a.v < b.v ? -1 : a.v > b.v ? 1 : 0; } // < and > compare a BigInt and a number exactly
  const toBig = x => { if (!isFinite(x)) throw evalErr('undefined'); return BigInt(x); };
  const roundBig = x => toBig(x < 0 ? -Math.round(-x) : Math.round(x));
  const floorDiv = (x, y) => { const q = x / y; return (x % y !== 0n) && ((x < 0n) !== (y < 0n)) ? q - 1n : q; };
  const now = (typeof performance !== 'undefined' && performance.now) ? () => performance.now() : () => Date.now();

  // ---------- text helpers ----------
  function textOf(t, what) {
    t = deref(t);
    switch (t.t) {
      case 'a': return t.n;
      case 's': return t.v;
      case 'n': return P.show(t);
      case 'v': throw instErr();
      case 'c': {
        const arr = listToArray(t);
        if (arr) {
          let s = '';
          for (let x of arr) { x = deref(x); if (x.t === 'n') s += String.fromCodePoint(x.v); else if (x.t === 'a') s += x.n; else if (x.t === 'v') throw instErr(); else throw typeError(what || 'text', t); }
          return s;
        }
      }
    }
    throw typeError(what || 'text', t);
  }
  function parseNumber(s) {
    const st = s.trim();
    if (!/^[+-]?(\d[\d_]*(\.\d+)?([eE][+-]?\d+)?|0x[0-9a-fA-F]+|0'.)$/.test(st) && !/^[+-]?(inf|nan)$/.test(st)) return null;
    try { const c = P.readTerm(st); const t = deref(c.term); if (t.t === 'n') return t; if (t.t === 'c' && t.f === '-' && t.a.length === 1 && deref(t.a[0]).t === 'n') { const x = deref(t.a[0]); return Num(-x.v, x.f); } if (t.t === 'c' && t.f === '+' && t.a.length === 1) return deref(t.a[0]); } catch (e) { }
    return null;
  }
  const charsList = s => list([...s].map(c => Atom(c)));
  const codesList = s => list([...s].map(c => Int(c.codePointAt(0))));

  // format/2 directives
  function format(fmt, argsT) {
    const f = textOf(fmt);
    let args = listToArray(argsT); if (!args) args = [argsT];
    let out = ''; let ai = 0; let lastCol = 0; const fills = [];
    const nextArg = () => { if (ai >= args.length) throw new PlError(Cmp('error', [Cmp('format', [Str('not enough arguments')]), Var()])); return args[ai++]; };
    for (let i = 0; i < f.length; i++) {
      const c = f[i];
      if (c !== '~') { out += c; continue; }
      i++; let num = '';
      while (i < f.length && /[0-9*]/.test(f[i])) { if (f[i] === '*') num += deref(nextArg()).v; else num += f[i]; i++; }
      if (f[i] === '`') { num = String(f[i + 1].codePointAt(0)); i += 2; }
      const d = f[i]; const n = num === '' ? null : parseInt(num, 10);
      switch (d) {
        case 'w': out += show(nextArg(), { quoted: false, swi: !!P.SWI_WRITE }); break;
        case 'p': out += show(nextArg(), { quoted: !!P.SWI_WRITE, swi: !!P.SWI_WRITE }); break;
        case 'q': out += show(nextArg(), { quoted: true, swi: !!P.SWI_WRITE }); break;
        case 'a': out += textOf(nextArg()); break;
        case 'd': { const x = deref(nextArg()); if (x.t !== 'n' || x.f) throw typeError('integer', x); if (n) { const s = String(x.v < 0 ? -x.v : x.v).padStart(n + 1, '0'); out += (x.v < 0 ? '-' : '') + s.slice(0, s.length - n) + '.' + s.slice(s.length - n); } else out += String(x.v); break; }
        case 'D': { const x = deref(nextArg()); out += String(x.v).replace(/\B(?=(\d{3})+(?!\d))/g, ','); break; }
        case 'f': case 'e': case 'g': { const x = evalArith(nextArg()); const v = Number(x.v); out += d === 'f' ? v.toFixed(n === null ? 6 : n) : d === 'e' ? v.toExponential(n === null ? 6 : n).replace(/e([+-])(\d)$/, 'e$10$2') : String(v); break; }
        case 'W': { const t = nextArg(), o = P.listToArray(nextArg()) || []; const has = (f, v) => o.some((x) => { x = deref(x); return x.t === 'c' && x.f === f && deref(x.a[0]).n === v; }); out += show(t, { quoted: has('quoted', 'true'), swi: !!P.SWI_WRITE, nextArg: has('spacing', 'next_argument') }); break; }
        case 's': out += textOf(nextArg()); break;
        case 'n': out += '\n'.repeat(n || 1); break;
        case 'c': { const x = deref(nextArg()); out += String.fromCodePoint(x.v).repeat(n || 1); break; }
        case 'r': { const x = deref(nextArg()); out += x.v.toString(n || 8); break; }
        case '~': out += '~'; break;
        case 't': fills.push(out.length); break;
        case '|': case '+': {
          const lineStart = out.lastIndexOf('\n') + 1;
          const colStart = Math.max(lineStart, lastCol);
          const target = d === '+' ? colStart + (n === null ? 8 : n) : lineStart + (n === null ? out.length - lineStart : n);
          const seg = out.slice(colStart); const pad = target - out.length;
          if (pad > 0) { if (fills.length) { const at = fills[fills.length - 1]; out = out.slice(0, at) + ' '.repeat(pad) + out.slice(at); } else if (d === '+') out = out.slice(0, colStart) + ' '.repeat(pad) + seg; else out += ' '.repeat(pad); }
          fills.length = 0; lastCol = out.length; break;
        }
        case 'i': nextArg(); break;
        default: out += '~' + d;
      }
    }
    return out;
  }

  // ---------- engine ----------
  const CONTROL = new Set([',/2', ';/2', '->/2', '*->/2', '!/0', 'true/0', 'fail/0', 'false/0', 'call/1', '\\+/1', 'not/1', 'findall/3', 'findall/4', 'forall/2', 'once/1', 'ignore/1', 'catch/3', 'throw/1', 'bagof/3', 'setof/3', 'aggregate_all/3', 'aggregate_all/4']);

  function Engine(prog, opts) {
    this.prog = prog; opts = opts || {};
    this.trail = []; this.markVid = Infinity;
    this.steps = 0; this.cpCreated = 0; this.maxCP = 0; this.out = '';
    this.stepLimit = opts.stepLimit || 5e6;
    this.globals = opts.globals || new Map();
    this.onOut = opts.onOut || null;
    // SWI-Prolog's I/O (src/swi.js): io = { out(s), err(s), readFile(p), writeFile(p, s, append), stat(p), list(p), stdin, argv, cwd }
    this.accel = opts.accel || null;
    this.io = opts.io || null; this.err = ''; this.onErr = opts.onErr || null; this.streams = new Map(); this.streamSeq = 0;
    this.flags = { occurs_check: false };
    this.depth = 0;
  }
  // a binding is trailed only when the variable is older than the newest mark (a choicepoint or a
  // builtin's undo point): a newer one is unreachable once older bindings are undone (as in the WAM),
  // so deterministic code does not grow the trail. Marks are taken with mark().
  Engine.prototype.bind = function (v, t) { v.ref = t; if (!(v.id > this.markVid)) this.trail.push(v); };
  Engine.prototype.mark = function () { this.markVid = P.varCount(); return this.trail.length; };
  Engine.prototype.undo = function (mark) { const tr = this.trail; while (tr.length > mark) tr.pop().ref = null; };
  Engine.prototype.unify = function (a, b) {
    const st = [a, b]; let n = 0, seen = null;
    while (st.length) {
      let y = deref(st.pop()), x = deref(st.pop());
      if (x === y) continue;
      // cyclic (rational) terms, as SWI-Prolog unifies them: after many steps, a pair of compounds
      // already being unified is taken as unified (co-induction), so the loop ends
      if (++n > 100000 && x.t === 'c' && y.t === 'c') {
        seen = seen || new Map(); let ys = seen.get(x);
        if (ys && ys.has(y)) continue;
        if (!ys) seen.set(x, ys = new Set()); ys.add(y);
      }
      // two variables: the newer is bound to the older (as in SWI-Prolog), so the standard order
      // of the older stays as it was, and the binding is less often trailed
      if (x.t === 'v') { if (y.t === 'v' && y.id > x.id) this.bind(y, x); else this.bind(x, y); continue; }
      if (y.t === 'v') { this.bind(y, x); continue; }
      if (x.t !== y.t) return false;
      switch (x.t) {
        case 'a': return false;
        case 'n': if (x.v !== y.v || x.f !== y.f) return false; continue;
        case 's': if (x.v !== y.v) return false; continue;
        case 'c':
          if (x.f !== y.f || x.a.length !== y.a.length) return false;
          for (let i = 0; i < x.a.length; i++) { st.push(x.a[i], y.a[i]); }
          continue;
      }
    }
    return true;
  };
  Engine.prototype.write = function (s) { this.out += s; if (this.onOut) this.onOut(s); };
  Engine.prototype.writeErr = function (s) { this.err += s; if (this.onErr) this.onErr(s); };

  // solve goal; calls onSol() for each solution; onSol returns true to continue.
  Engine.prototype.solve = function (goal, onSol, depthCut) {
    this.depth++;
    if (this.depth > 400) { this.depth--; throw new LimitError('nesting limit (findall/\\+/call depth) exceeded'); }
    try { return this._run(goal, onSol); } finally { this.depth--; }
  };
  Engine.prototype._run = function (goal, onSol) {
    const self = this;
    const cps = [];
    let goals = { g: goal, cb: 0, next: null };
    const base = 0;
    const builtins = P.builtins;
    const push = cp => { cps.push(cp); self.cpCreated++; if (cps.length > self.maxCP) self.maxCP = cps.length; };
    let stopped = false;
    const backtrack = () => {
      for (;;) {
        if (cps.length === base) return false;
        const cp = cps[cps.length - 1];
        self.undo(cp.trail);
        if (cp.kind === 'alt') { cps.pop(); goals = cp.goals; return true; }
        if (cp.kind === 'clauses') {
          const res = self.tryClauses(cp.goal, cp.clauses, cp.idx, cp.next, cp.cb, cps, cp);
          if (res) { goals = res; return true; }
          continue;
        }
        if (cp.kind === 'gen') {
          const r = cp.it.next();
          if (!r.done) { goals = cp.next; return true; }
          cps.pop(); continue;
        }
        if (cp.kind === 'barrier' || cp.kind === 'catch') { cps.pop(); continue; }
        cps.pop();
      }
    };
    for (;;) {
      if (goals === null) {
        const more = onSol();
        if (!more) { stopped = true; return true; }
        if (!backtrack()) return false;
        continue;
      }
      const fr = goals; goals = fr.next;
      let g = deref(fr.g);
      if (++self.steps > self.stepLimit) throw new LimitError('step limit (' + String(self.stepLimit) + ') exceeded');
      try {
        if (g.t === 'v') throw instErr();
        let f, n, a;
        if (g.t === 'a') { f = g.n; n = 0; a = []; }
        else if (g.t === 'c') { f = g.f; n = g.a.length; a = g.a; }
        else throw typeError('callable', g);
        const k = f + '/' + n;
        switch (k) {
          case 'true/0': continue;
          case 'fail/0': case 'false/0': if (!backtrack()) return false; continue;
          case ',/2': self.steps--; goals = { g: a[0], cb: fr.cb, next: { g: a[1], cb: fr.cb, next: goals } }; continue;
          case '!/0': cps.length = Math.max(fr.cb, base); continue;
          case ';/2': {
            const l = deref(a[0]);
            if (l.t === 'c' && l.f === '->' && l.a.length === 2) {
              const B = cps.length;
              push({ kind: 'alt', goals: { g: a[1], cb: fr.cb, next: goals }, trail: self.mark() });
              goals = { g: l.a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: { g: l.a[1], cb: fr.cb, next: goals } } };
              continue;
            }
            if (l.t === 'c' && l.f === '*->' && l.a.length === 2) {
              const alt = { kind: 'alt', goals: { g: a[1], cb: fr.cb, next: goals }, trail: self.mark() };
              push(alt);
              goals = { g: l.a[0], cb: cps.length, next: { g: Cmp('$softcut', [{ t: 'n', v: 0, cp: alt }]), cb: fr.cb, next: { g: l.a[1], cb: fr.cb, next: goals } } };
              continue;
            }
            push({ kind: 'alt', goals: { g: a[1], cb: fr.cb, next: goals }, trail: self.mark() });
            goals = { g: a[0], cb: fr.cb, next: goals };
            continue;
          }
          case '->/2': {
            const B = cps.length;
            push({ kind: 'barrier', trail: self.mark() });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: { g: a[1], cb: fr.cb, next: goals } } };
            continue;
          }
          case '*->/2': goals = { g: a[0], cb: cps.length, next: { g: a[1], cb: fr.cb, next: goals } }; continue;
          case '$ite/1': cps.length = deref(a[0]).v; continue;
          case '$softcut/1': { const alt = a[0].cp; const i = cps.indexOf(alt); if (i >= 0) cps[i] = { kind: 'barrier', trail: alt.trail }; continue; }
          case '\\+/1': case 'not/1': {
            const B = cps.length;
            push({ kind: 'alt', goals: goals, trail: self.mark() });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: { g: P.FAIL, cb: fr.cb, next: null } } };
            continue;
          }
          case 'call/1': goals = { g: a[0], cb: cps.length, next: goals }; continue;
          case 'once/1': {
            const B = cps.length;
            push({ kind: 'barrier', trail: self.mark() });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: goals } };
            continue;
          }
          case 'ignore/1': {
            const B = cps.length;
            push({ kind: 'alt', goals: goals, trail: self.mark() });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: goals } };
            continue;
          }
          case 'forall/2': {
            let ok = true; const mark = self.mark();
            self.solve(a[0], () => { let s = false; const m2 = self.mark(); self.solve(a[1], () => { s = true; return false; }); self.undo(m2); if (!s) { ok = false; return false; } return true; });
            self.undo(mark);
            if (!ok && !backtrack()) return false; continue;
          }
          case 'findall/3': case 'findall/4': {
            const res = []; const mark = self.mark();
            self.solve(a[1], () => { res.push(copy(a[0])); return true; });
            self.undo(mark);
            if (!self.unify(a[2], list(res, n === 4 ? a[3] : NIL))) { if (!backtrack()) return false; }
            continue;
          }
          case 'bagof/3': case 'setof/3': {
            // grouping by free variables (^ supported)
            let gl = deref(a[1]); const exVars = [];
            while (gl.t === 'c' && gl.f === '^' && gl.a.length === 2) { termVars(gl.a[0], exVars); gl = deref(gl.a[1]); }
            const tv = termVars(a[0]); const ex = new Set(tv.concat(exVars));
            const free = termVars(gl).filter(v => !ex.has(v));
            const W = list(free);
            const res = []; const mark = self.mark();
            self.solve(gl, () => { res.push(copy(Cmp('-', [W, a[0]]))); return true; });
            self.undo(mark);
            if (!res.length) { if (!backtrack()) return false; continue; }
            // group
            const groups = [];
            if (free.length === 0) groups.push({ w: W, items: res.map(r => r.a[1]) });
            else {
              const sorted = k === 'setof/3' ? res.slice().sort((x, y) => compare(x.a[0], y.a[0])) : res.slice().sort((x, y) => compare(x.a[0], y.a[0]));
              for (const r of sorted) { const gq = groups.find(gq => P.variantKey(gq.w) === P.variantKey(r.a[0])); if (gq) gq.items.push(r.a[1]); else groups.push({ w: r.a[0], items: [r.a[1]] }); }
            }
            const alts = groups.map(gq => {
              let items = gq.items;
              if (k === 'setof/3') items = sortUnique(items);
              return Cmp(',', [Cmp('=', [W, gq.w]), Cmp('=', [a[2], list(items)])]);
            });
            goals = { g: disj(alts), cb: fr.cb, next: goals };
            continue;
          }
          case 'aggregate_all/3': {
            const spec = deref(a[0]); const res = []; const mark = self.mark();
            const sk = P.key(spec);
            const tmpl = sk === 'count/0' ? P.TRUE : spec.t === 'c' ? spec.a[0] : P.TRUE;
            self.solve(a[1], () => { res.push(copy(tmpl)); return true; });
            self.undo(mark);
            let r;
            switch (sk) {
              case 'count/0': r = Int(res.length); break;
              case 'count/1': r = Int(res.length); break;
              case 'sum/1': { let s = Int(0); for (const x of res) s = evalArith(Cmp('+', [s, x])); r = s; break; }
              case 'max/1': if (!res.length) { r = null; break; } r = res.map(evalArith).reduce((m, x) => x.v > m.v ? x : m); break;
              case 'min/1': if (!res.length) { r = null; break; } r = res.map(evalArith).reduce((m, x) => x.v < m.v ? x : m); break;
              case 'bag/1': r = list(res); break;
              case 'set/1': r = list(sortUnique(res)); break;
              default: throw typeError('aggregate_spec', spec);
            }
            if (r === null || !self.unify(a[2], r)) { if (!backtrack()) return false; }
            continue;
          }
          case 'catch/3': {
            push({ kind: 'catch', catcher: a[1], recovery: a[2], next: goals, cb: fr.cb, trail: self.mark() });
            goals = { g: a[0], cb: cps.length, next: goals };
            continue;
          }
          case 'throw/1': throw new PlError(copy(a[0]));
          case 'with_output_to/2': {
            const save = self.out, saveOn = self.onOut; self.out = ''; self.onOut = null; let ok = false; const mark = self.mark();
            try { self.solve(a[1], () => { ok = true; return false; }); } finally { var txt = self.out; self.out = save; self.onOut = saveOn; }
            const sk = deref(a[0]);
            if (!ok) { self.undo(mark); if (!backtrack()) return false; continue; }
            const v = sk.f === 'atom' ? Atom(txt) : sk.f === 'string' ? Str(txt) : sk.f === 'codes' ? P.codesList(txt) : P.charsList(txt);
            if (!self.unify(sk.a[0], v)) { if (!backtrack()) return false; }
            continue;
          }
        }
        if (k.startsWith('call/') && n > 1) {
          const c = deref(a[0]); const extra = a.slice(1);
          let ng;
          const cq = c.t === 'c' && c.f === ':' && c.a.length === 2 ? deref(c.a[1]) : null; // call(M:G, X): M:G(X)
          if (cq) ng = Cmp(':', [c.a[0], cq.t === 'a' ? Cmp(cq.n, extra) : cq.t === 'c' ? Cmp(cq.f, cq.a.concat(extra)) : Cmp('call', [cq].concat(extra))]);
          else if (c.t === 'a') ng = Cmp(c.n, extra); else if (c.t === 'c') ng = Cmp(c.f, c.a.concat(extra)); else if (c.t === 'v') throw instErr(); else throw typeError('callable', c);
          goals = { g: ng, cb: cps.length, next: goals };
          continue;
        }
        // lib: a library call (lists:reverse(..)) goes to the built-in even when a module exports the name
        const clauses = g.lib ? null : self.prog.preds.get(k);
        // a faster route for this call (the interpreter's: src/interp.js), as a generator of its answers
        if (clauses && self.accel) {
          const it = self.accel(k, g, self);
          if (it) {
            const mark = self.mark();
            const r = it.next();
            if (r.done) { self.undo(mark); if (!backtrack()) return false; continue; }
            if (r.value !== 'last') push({ kind: 'gen', it, next: goals, trail: mark });
            continue;
          }
        }
        if (clauses) {
          const res = self.tryClauses(g, clauses, 0, goals, null, cps, null, push);
          if (res) { goals = res; continue; }
          if (!backtrack()) return false;
          continue;
        }
        const bi = builtins[k];
        if (bi) {
          if (bi.nondet) {
            const it = bi.fn(a, self, g);
            const mark = self.mark();
            const r = it.next();
            if (r.done) { self.undo(mark); if (!backtrack()) return false; continue; }
            if (r.value === 'last') continue; // deterministic exit
            push({ kind: 'gen', it, next: goals, trail: mark });
            continue;
          }
          if (bi.call) { // builtin that expands into a goal
            const ng = bi.fn(a, self, g);
            if (ng === null) { if (!backtrack()) return false; continue; }
            goals = { g: ng, cb: cps.length, next: goals };
            continue;
          }
          const mark = self.trail.length; // a failed builtin backtracks anyway: no new mark needed
          if (!bi.fn(a, self, g)) { self.undo(mark); if (!backtrack()) return false; }
          continue;
        }
        if (self.prog.dynamic.has(k)) { if (!backtrack()) return false; continue; }
        // a goal built at run time that names a module's private predicate (src/swi.js)
        if (self.prog.privates && self.prog.privates.has(k)) { const nm = self.prog.privates.get(k)[0]; goals = { g: g.t === 'a' ? Atom(nm) : Cmp(nm, a), cb: cps.length, next: goals }; continue; }
        throw existErr(k);
      } catch (e) {
        // a syntax error from reading text (term_string/2, read_term/2, ...) is a Prolog error that catch/3 sees
        if (e && e.prolog && !(e instanceof PlError) && /^Syntax error/.test(e.message)) e = new PlError(P.Cmp('error', [P.Cmp('syntax_error', [P.Atom(String(e.message).replace(/^Syntax error( \(line \d+\))?: /, ''))]), P.Var()]));
        if (!(e instanceof PlError)) throw e;
        // find catch frame
        let handled = false;
        while (cps.length > base) {
          const cp = cps.pop();
          if (cp.kind === 'catch') {
            self.undo(cp.trail);
            const mark = self.mark();
            const ball = copy(e.term);
            if (self.unify(cp.catcher, ball)) { goals = { g: cp.recovery, cb: cp.cb, next: cp.next }; handled = true; break; }
            self.undo(mark);
          }
        }
        if (!handled) throw e;
      }
    }
  };
  function disj(alts) { if (!alts.length) return P.FAIL; let r = alts[alts.length - 1]; for (let i = alts.length - 2; i >= 0; i--) r = Cmp(';', [alts[i], r]); return r; }
  function sortUnique(items) { const s = items.slice().sort(compare); const out = []; for (const x of s) if (!out.length || compare(out[out.length - 1], x) !== 0) out.push(x); return out; }

  // first-argument indexing compatible?
  function firstArgMayMatch(goalArg, headArg) {
    const g = deref(goalArg), h = deref(headArg);
    if (g.t === 'v' || h.t === 'v') return true;
    if (g.t !== h.t) return false;
    if (g.t === 'a') return g.n === h.n;
    if (g.t === 'n') return g.v === h.v;
    if (g.t === 's') return g.v === h.v;
    return g.f === h.f && g.a.length === h.a.length;
  }
  Engine.prototype.tryClauses = function (g, clauses, start, next, cbIn, cps, cp, push) {
    const self = this;
    const ga = g.t === 'c' ? g.a : null;
    const fa = ga ? ga[0] : null;
    // find first candidate from start
    let i = start;
    const cand = j => !fa || firstArgMayMatch(fa, clauses[j].head.a[0]);
    while (i < clauses.length && !cand(i)) i++;
    if (i >= clauses.length) { if (cp) cps.pop(); return null; }
    for (;;) {
      let j = i + 1; while (j < clauses.length && !cand(j)) j++;
      const hasMore = j < clauses.length;
      const cb = cp ? cp.cb : cps.length;
      if (cp) { if (hasMore) { cp.idx = j; } else cps.pop(); }
      else if (hasMore) { cp = { kind: 'clauses', goal: g, clauses, idx: j, next, cb, trail: self.mark() }; push(cp); }
      const cl = clauses[i];
      const m = new Map();
      const h = copy(cl.head, m);
      // the goal's variables are older than this call's choicepoint (or need no undo without one):
      // the trail's length is enough to undo a failed head unification
      const mark = self.trail.length;
      if (self.unify(h, g)) {
        const body = deref(cl.body);
        if (body.t === 'a' && body.n === 'true') return next === null ? { g: P.TRUE, cb, next: null } : next;
        return { g: copy(body, m), cb, next };
      }
      self.undo(mark);
      if (!hasMore) return null;
      i = j;
      if (cp && cps[cps.length - 1] !== cp) return null;
    }
  };

  // ---------- running queries ----------
  // returns { ok, answers:[{text, bindings}], events:[{k:'row'|'out', text}], output, steps, cps, maxCP, timeMs, error }
  function runQuery(prog, queryText, opts) {
    opts = opts || {};
    if (typeof prog === 'string') prog = loadProgram(prog);
    const q = typeof queryText === 'string' ? P.readTerm(queryText) : queryText;
    if (P.expandDots && P.hasDots(q.term)) q.term = P.expandDots(Cmp(':-', [Atom('$q'), q.term])).a[1];
    const vars = q.vars.filter(([nm]) => !nm.startsWith('_'));
    const eng = new Engine(prog, opts);
    const maxAnswers = opts.maxAnswers || 1000;
    const answers = [], events = [];
    let lastOut = 0, error = null, limit = false, halted = null;
    const t0 = now();
    try {
      runInitGlobals(eng, prog);
      eng.solve(q.term, () => {
        if (eng.out.length > lastOut) { events.push({ k: 'out', text: eng.out.slice(lastOut) }); lastOut = eng.out.length; }
        const nm = P.namer();
        const text = vars.length ? vars.map(([n, v]) => n + ' = ' + show(v, { varName: nm })).join(', ') : 'true';
        answers.push({ text }); events.push({ k: 'row', text });
        return answers.length < maxAnswers;
      });
    } catch (e) { if (e && e.halt) { halted = e.code; } else error = e.limit ? e.message : e.prolog ? (e.term ? errText(e.term) : e.message) : e.message; limit = !!e.limit; if (!e.prolog && !e.limit && (opts.debug || (typeof process !== "undefined" && process.env && process.env.PL2DETLOG_DEBUG))) console.error(e); }
    const t1 = now();
    eng.undo(0); // leave the (possibly reused) query term unbound
    if (eng.out.length > lastOut) events.push({ k: 'out', text: eng.out.slice(lastOut) });
    if (P.closeStreams) P.closeStreams(eng);
    return { ok: !error, answers, events, output: eng.out, errOutput: eng.err, halted, steps: eng.steps, cps: eng.cpCreated, maxCP: eng.maxCP, timeMs: t1 - t0, error, limit, truncated: answers.length >= maxAnswers };
  }
  function runInitGlobals() { }
  function errText(t) { t = deref(t); if (t.t === 'c' && t.f === 'error' && t.a.length === 2) return show(t.a[0], { varName: P.namer() }); return 'uncaught ' + show(t, { varName: P.namer() }); }
  P.errText = errText;

  Object.assign(P, { Engine, Program, loadProgram, runQuery, evalArith, textOf, parseNumber, charsList, codesList, format, PlError, LimitError, typeError, instErr, commaList, CONTROL, now, sortUnique, disj, firstArgMayMatch, dcgTransform });
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog builtins for the reference engine. det: fn(args, eng) -> bool.
   nondet: generator fn yielding once per solution (bindings made before yield). */
(function (P) {
  'use strict';
  const { Atom, Num, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, isNil, listToArray, copy, termVars, isGround, compare, show, evalArith, textOf, parseNumber, charsList, codesList, typeError, instErr, PlError, sortUnique } = P;
  const B = {};
  const det = (k, fn) => { B[k] = { fn }; };
  const nondet = (k, fn) => { B[k] = { fn, nondet: true }; };
  const callb = (k, fn) => { B[k] = { fn, call: true }; };
  const D = deref;
  const arr = (t) => { const a = listToArray(t); if (!a) { if (D(t).t === 'v') throw instErr(); throw typeError('list', t); } return a; };
  const add = (x, k) => evalArith(Cmp('+', [x, Int(k)]));
  const numCmp = (a, b) => { const x = evalArith(a), y = evalArith(b); return x.v < y.v ? -1 : x.v > y.v ? 1 : 0; };

  // type checks
  det('var/1', a => D(a[0]).t === 'v');
  det('nonvar/1', a => D(a[0]).t !== 'v');
  det('atom/1', a => D(a[0]).t === 'a');
  det('number/1', a => D(a[0]).t === 'n');
  det('integer/1', a => { const x = D(a[0]); return x.t === 'n' && !x.f; });
  det('float/1', a => { const x = D(a[0]); return x.t === 'n' && x.f; });
  det('atomic/1', a => { const x = D(a[0]); return x.t === 'a' || x.t === 'n' || x.t === 's'; });
  det('compound/1', a => D(a[0]).t === 'c');
  det('callable/1', a => { const x = D(a[0]); return x.t === 'a' || x.t === 'c'; });
  det('is_list/1', a => listToArray(a[0]) !== null);
  det('string/1', a => D(a[0]).t === 's');
  det('ground/1', a => isGround(a[0]));
  det('is_dict/1', () => false);
  det('is_assoc/1', () => false);

  // unification / comparison
  det('=/2', (a, e) => e.unify(a[0], a[1]));
  det('\\=/2', (a, e) => { const m = e.mark(); const r = e.unify(a[0], a[1]); e.undo(m); return !r; });
  det('unify_with_occurs_check/2', (a, e) => e.unify(a[0], a[1]));
  det('==/2', a => compare(a[0], a[1]) === 0);
  det('\\==/2', a => compare(a[0], a[1]) !== 0);
  det('@</2', a => compare(a[0], a[1]) < 0);
  det('@>/2', a => compare(a[0], a[1]) > 0);
  det('@=</2', a => compare(a[0], a[1]) <= 0);
  det('@>=/2', a => compare(a[0], a[1]) >= 0);
  det('compare/3', (a, e) => { const c = compare(a[1], a[2]); return e.unify(a[0], Atom(c < 0 ? '<' : c > 0 ? '>' : '=')); });
  det('is/2', (a, e) => e.unify(a[0], evalArith(a[1])));
  det('=:=/2', a => numCmp(a[0], a[1]) === 0);
  det('=\\=/2', a => numCmp(a[0], a[1]) !== 0);
  det('</2', a => numCmp(a[0], a[1]) < 0);
  det('>/2', a => numCmp(a[0], a[1]) > 0);
  det('=</2', a => numCmp(a[0], a[1]) <= 0);
  det('>=/2', a => numCmp(a[0], a[1]) >= 0);
  det('succ/2', (a, e) => { const x = D(a[0]); if (x.t === 'n') return e.unify(a[1], add(x, 1)); const y = D(a[1]); if (y.t === 'v') throw instErr(); if (y.v <= 0) return false; return e.unify(a[0], add(y, -1)); });
  det('plus/3', (a, e) => { const x = D(a[0]), y = D(a[1]), z = D(a[2]); const ar = (f, p, q) => evalArith(Cmp(f, [p, q])); if (x.t === 'n' && y.t === 'n') return e.unify(z, ar('+', x, y)); if (x.t === 'n' && z.t === 'n') return e.unify(y, ar('-', z, x)); if (y.t === 'n' && z.t === 'n') return e.unify(x, ar('-', z, y)); throw instErr(); });

  // terms
  det('functor/3', (a, e) => {
    const t = D(a[0]);
    if (t.t === 'v') { const n = D(a[2]).v; const nm = D(a[1]); if (n === 0) return e.unify(t, nm); const args = []; for (let i = 0; i < n; i++) args.push(Var()); return e.unify(t, Cmp(nm.n, args)); }
    if (t.t === 'c') return e.unify(a[1], Atom(t.f)) && e.unify(a[2], Int(t.a.length));
    return e.unify(a[1], t) && e.unify(a[2], Int(0));
  });
  nondet('arg/3', function* (a, e) {
    const n = D(a[0]), t = D(a[1]);
    if (t.t !== 'c') throw typeError('compound', t);
    if (n.t === 'n') { if (n.v >= 1 && n.v <= t.a.length && e.unify(a[2], t.a[n.v - 1])) yield 'last'; return; }
    for (let i = 0; i < t.a.length; i++) { const m = e.mark(); if (e.unify(n, Int(i + 1)) && e.unify(a[2], t.a[i])) yield; e.undo(m); }
  });
  det('=../2', (a, e) => {
    const t = D(a[0]);
    if (t.t === 'c') return e.unify(a[1], list([Atom(t.f)].concat(t.a)));
    if (t.t !== 'v') return e.unify(a[1], list([t]));
    const l = arr(a[1]); const h = D(l[0]);
    if (l.length === 1) return e.unify(t, h);
    return e.unify(t, Cmp(h.n, l.slice(1)));
  });
  det('copy_term/2', (a, e) => e.unify(a[1], copy(a[0])));
  det('numbervars/3', (a, e) => { let n = D(a[1]).v; for (const v of termVars(a[0])) e.bind(v, Cmp('$VAR', [Int(n++)])); return e.unify(a[2], Int(n)); });
  det('term_variables/2', (a, e) => e.unify(a[1], list(termVars(a[0]))));
  det('setarg/3', (a) => { const t = D(a[1]); t.a[D(a[0]).v - 1] = copy(a[2]); return true; });
  det('nb_setarg/3', (a) => { const t = D(a[1]); t.a[D(a[0]).v - 1] = copy(a[2]); return true; });
  det('term_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Atom(show(t))); return e.unify(t, P.readTerm(textOf(a[1])).term); });
  det('term_string/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Str(show(t))); return e.unify(t, P.readTerm(textOf(a[1])).term); });
  det('read_term_from_atom/3', (a, e) => e.unify(a[1], P.readTerm(textOf(a[0])).term));
  det('tab/1', (a, e) => { e.write(' '.repeat(evalArith(a[0]).v)); return true; });

  // output
  det('write/1', (a, e) => { e.write(show(a[0], { quoted: false })); return true; });
  det('print/1', (a, e) => { e.write(show(a[0], { quoted: true })); return true; });
  det('writeln/1', (a, e) => { e.write(show(a[0], { quoted: false }) + '\n'); return true; });
  det('writeq/1', (a, e) => { e.write(show(a[0], { quoted: true })); return true; });
  det('write_canonical/1', (a, e) => { e.write(show(a[0], { quoted: true, ignoreOps: true })); return true; });
  det('write_term/2', (a, e) => { e.write(show(a[0], { quoted: false })); return true; });
  det('nl/0', (a, e) => { e.write('\n'); return true; });
  det('put_char/1', (a, e) => { e.write(D(a[0]).n); return true; });
  det('format/1', (a, e) => { e.write(P.format(a[0], NIL)); return true; });
  det('format/2', (a, e) => { e.write(P.format(a[0], a[1])); return true; });
  det('format/3', (a, e) => {
    const s = D(a[0]); const txt = P.format(a[1], a[2]);
    if (s.t === 'c' && s.a.length === 1) {
      const k = s.f; const v = k === 'atom' ? Atom(txt) : k === 'string' ? Str(txt) : k === 'codes' ? codesList(txt) : k === 'chars' ? charsList(txt) : null;
      if (v) return e.unify(s.a[0], v);
    }
    e.write(txt); return true;
  });
  det('flush_output/0', () => true);
  // halt is not an error: no catch/3 sees it; the run stops with its exit code
  det('halt/0', () => { throw { halt: true, code: 0 }; });
  det('halt/1', (a) => { const c = evalArith(a[0]); throw { halt: true, code: Number(c.v) }; });

  // atoms & strings
  // the text of a code or char list; [] is the empty text (not the atom '[]')
  const listText = (x) => { const t = D(x); return t.t === 'a' && t.n === '[]' ? '' : textOf(t); };
  det('atom_codes/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], codesList(textOf(t))); return e.unify(t, Atom(listText(a[1]))); });
  det('atom_chars/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], charsList(textOf(t))); return e.unify(t, Atom(listText(a[1]))); });
  det('char_code/2', (a, e) => { const t = D(a[0]); if (t.t === 'a') return e.unify(a[1], Int(t.n.codePointAt(0))); return e.unify(t, Atom(String.fromCodePoint(D(a[1]).v))); });
  det('atom_length/2', (a, e) => e.unify(a[1], Int([...textOf(a[0])].length)));
  det('string_length/2', (a, e) => e.unify(a[1], Int([...textOf(a[0])].length)));
  det('atom_number/2', (a, e) => { const t = D(a[0]); if (t.t === 'v') { const n = D(a[1]); if (n.t === 'v') throw instErr(); return e.unify(t, Atom(show(n))); } const n = parseNumber(textOf(t)); return n ? e.unify(a[1], n) : false; });
  det('number_codes/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], codesList(show(t))); const n = parseNumber(textOf(a[1])); if (!n) throw new PlError(Cmp('error', [Cmp('syntax_error', [Atom('illegal_number')]), Var()])); return e.unify(t, n); });
  det('number_chars/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], charsList(show(t))); const n = parseNumber(textOf(a[1])); if (!n) throw new PlError(Cmp('error', [Cmp('syntax_error', [Atom('illegal_number')]), Var()])); return e.unify(t, n); });
  det('number_string/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Str(show(t))); const n = parseNumber(textOf(a[1])); return n ? e.unify(t, n) : false; });
  det('atom_string/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Str(textOf(t))); return e.unify(t, Atom(textOf(a[1]))); });
  det('number_vars/3', () => true);
  det('string_chars/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], charsList(textOf(t))); return e.unify(t, Str(listText(a[1]))); });
  det('string_codes/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], codesList(textOf(t))); return e.unify(t, Str(listText(a[1]))); });
  det('string_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Atom(textOf(t))); return e.unify(t, Str(textOf(a[1]))); });
  det('string_code/3', (a, e) => { const s = [...textOf(a[1])]; const i = D(a[0]).v; if (i < 1 || i > s.length) return false; return e.unify(a[2], Int(s[i - 1].codePointAt(0))); });
  det('number_codes/2', B['number_codes/2'].fn);
  det('string/1', a => D(a[0]).t === 's');
  det('text_concat/3', (a, e) => e.unify(a[2], Atom(textOf(a[0]) + textOf(a[1]))));
  det('string_number/2', (a, e) => { const n = parseNumber(textOf(a[0])); return n ? e.unify(a[1], n) : false; });
  det('term_string/3', B['term_string/2'].fn);
  det('upcase_atom/2', (a, e) => e.unify(a[1], Atom(textOf(a[0]).toUpperCase())));
  det('downcase_atom/2', (a, e) => e.unify(a[1], Atom(textOf(a[0]).toLowerCase())));
  det('string_upper/2', (a, e) => e.unify(a[1], Str(textOf(a[0]).toUpperCase())));
  det('string_lower/2', (a, e) => e.unify(a[1], Str(textOf(a[0]).toLowerCase())));
  det('normalize_space/2', (a, e) => { const s = textOf(a[1]).trim().split(/\s+/).join(' '); const sp = D(a[0]); const k = sp.f; return e.unify(sp.a[0], k === 'atom' ? Atom(s) : k === 'string' ? Str(s) : k === 'codes' ? codesList(s) : charsList(s)); });
  det('split_string/4', (a, e) => {
    const s = textOf(a[0]), sep = textOf(a[1]), pad = textOf(a[2]);
    const parts = []; let cur = '';
    if (sep.length === 0) parts.push(s); else { for (const c of s) { if (sep.includes(c)) { parts.push(cur); cur = ''; } else cur += c; } parts.push(cur); }
    const strip = x => { let i = 0, j = x.length; while (i < j && pad.includes(x[i])) i++; while (j > i && pad.includes(x[j - 1])) j--; return x.slice(i, j); };
    return e.unify(a[3], list(parts.map(p => Str(strip(p)))));
  });
  det('atomic_list_concat/2', (a, e) => e.unify(a[1], Atom(arr(a[0]).map(x => textOf(x)).join(''))));
  det('atomic_list_concat/3', (a, e) => {
    const sep = textOf(a[1]); const l = listToArray(a[0]);
    if (l && l.every(x => D(x).t !== 'v')) return e.unify(a[2], Atom(l.map(x => textOf(x)).join(sep)));
    if (sep === '') throw instErr();
    return e.unify(a[0], list(textOf(a[2]).split(sep).map(x => Atom(x))));
  });
  nondet('string_concat/3', function* (a, e) {
    const x = D(a[0]), y = D(a[1]);
    if (x.t !== 'v' && y.t !== 'v') { if (e.unify(a[2], Str(textOf(x) + textOf(y)))) yield 'last'; return; }
    const z = textOf(a[2]);
    if (x.t !== 'v') { const p = textOf(x); if (z.startsWith(p) && e.unify(y, Str(z.slice(p.length)))) yield 'last'; return; }
    if (y.t !== 'v') { const q = textOf(y); if (z.endsWith(q) && e.unify(x, Str(z.slice(0, z.length - q.length)))) yield 'last'; return; }
    const cs = [...z];
    for (let i = 0; i <= cs.length; i++) { const m = e.mark(); if (e.unify(x, Str(cs.slice(0, i).join(''))) && e.unify(y, Str(cs.slice(i).join('')))) yield; e.undo(m); }
  });
  nondet('atom_concat/3', function* (a, e) {
    const x = D(a[0]), y = D(a[1]);
    if (x.t !== 'v' && y.t !== 'v') { if (e.unify(a[2], Atom(textOf(x) + textOf(y)))) yield 'last'; return; }
    const z = [...textOf(a[2])];
    for (let i = 0; i <= z.length; i++) { const m = e.mark(); if (e.unify(x, Atom(z.slice(0, i).join(''))) && e.unify(y, Atom(z.slice(i).join('')))) yield; e.undo(m); }
  });
  function* subText(a, e, mk) {
    const s = [...textOf(a[0])]; const n = s.length;
    const Bf = D(a[1]), L = D(a[2]), Af = D(a[3]), Sub = D(a[4]);
    if (Sub.t !== 'v') {
      const sub = [...textOf(Sub)]; const k = sub.length; const subs = sub.join('');
      for (let i = 0; i + k <= n; i++) if (s.slice(i, i + k).join('') === subs) { const m = e.mark(); if (e.unify(Bf, Int(i)) && e.unify(L, Int(k)) && e.unify(Af, Int(n - i - k))) yield; e.undo(m); }
      return;
    }
    for (let i = 0; i <= n; i++) {
      if (Bf.t === 'n' && Bf.v !== i) continue;
      for (let k = 0; i + k <= n; k++) {
        if (L.t === 'n' && L.v !== k) continue;
        if (Af.t === 'n' && Af.v !== n - i - k) continue;
        const m = e.mark();
        if (e.unify(Bf, Int(i)) && e.unify(L, Int(k)) && e.unify(Af, Int(n - i - k)) && e.unify(Sub, mk(s.slice(i, i + k).join('')))) yield;
        e.undo(m);
      }
    }
  }
  nondet('sub_atom/5', function* (a, e) { yield* subText(a, e, Atom); });
  nondet('sub_string/5', function* (a, e) { yield* subText(a, e, Str); });
  nondet('char_type/2', function* (a, e) {
    const c = D(a[0]); const ty = D(a[1]);
    if (c.t === 'v') throw instErr();
    const ch = c.t === 'n' ? String.fromCodePoint(c.v) : c.n;
    const tn = ty.t === 'a' ? ty.n : ty.f;
    let ok = null;
    switch (tn) {
      case 'alpha': ok = /[\p{L}\p{N}_]/u.test(ch); break;
      case 'alnum': ok = /[\p{L}\p{N}]/u.test(ch); break;
      case 'digit': if (ty.t === 'c') { if (/[0-9]/.test(ch)) { if (e.unify(ty.a[0], Int(+ch))) yield 'last'; } return; } ok = /[0-9]/.test(ch); break;
      case 'xdigit': { const w = /^[0-9a-fA-F]$/.test(ch) ? parseInt(ch, 16) : -1; if (ty.t === 'c') { if (w >= 0 && e.unify(ty.a[0], Int(w))) yield 'last'; return; } ok = w >= 0; break; }
      case 'space': case 'white': ok = /\s/.test(ch); break;
      case 'upper': if (ty.t === 'c') { if (ch !== ch.toLowerCase() || /[A-Z]/.test(ch)) { if (e.unify(ty.a[0], Atom(ch.toLowerCase()))) yield 'last'; } return; } ok = /\p{Lu}/u.test(ch); break;
      case 'lower': if (ty.t === 'c') { if (/\p{Ll}/u.test(ch)) { if (e.unify(ty.a[0], Atom(ch.toUpperCase()))) yield 'last'; } return; } ok = /\p{Ll}/u.test(ch); break;
      case 'punct': ok = /[!-\/:-@\[-`{-~]/.test(ch); break;
      case 'csym': ok = /[A-Za-z0-9_]/.test(ch); break;
      case 'csymf': ok = /[A-Za-z_]/.test(ch); break;
      case 'end_of_line': ok = /[\n\r]/.test(ch); break;
      case 'graph': ok = /[!-~]/.test(ch) && !/[A-Za-z0-9]/.test(ch); break;
      case 'to_lower': if (e.unify(ty.a[0], Atom(ch.toLowerCase()))) yield 'last'; return;
      case 'to_upper': if (e.unify(ty.a[0], Atom(ch.toUpperCase()))) yield 'last'; return;
    }
    if (ok) yield 'last';
  });
  det('code_type/2', (a, e) => { const c = D(a[0]); const ch = c.t === 'n' ? String.fromCodePoint(c.v) : c.n; const ty = P.name(a[1]); if (ty === 'digit' && D(a[1]).t === 'c') return /[0-9]/.test(ch) && e.unify(D(a[1]).a[0], Int(+ch)); if (ty === 'xdigit' && D(a[1]).t === 'c') return /^[0-9a-fA-F]$/.test(ch) && e.unify(D(a[1]).a[0], Int(parseInt(ch, 16))); const re = { xdigit: /^[0-9a-fA-F]$/, alpha: /[A-Za-z0-9_]/, alnum: /[A-Za-z0-9]/, digit: /[0-9]/, space: /\s/, white: /[ \t]/, upper: /[A-Z]/, lower: /[a-z]/, punct: /[!-\/:-@\[-`{-~]/, csym: /[A-Za-z0-9_]/, csymf: /[A-Za-z_]/ }[ty]; return re ? re.test(ch) : false; });

  // lists
  nondet('between/3', function* (a, e) {
    const lo = evalArith(a[0]).v, hiT = D(a[1]); const hi = hiT.t === 'a' && (hiT.n === 'inf' || hiT.n === 'infinite') ? Infinity : evalArith(hiT).v;
    const x = D(a[2]);
    if (x.t === 'n') { if (x.v >= lo && x.v <= hi) yield 'last'; return; }
    for (let i = lo; i <= hi; i++) { const m = e.mark(); if (e.unify(x, Int(i))) yield i === hi ? 'last' : undefined; e.undo(m); }
  });
  nondet('member/2', function* (a, e) {
    let l = D(a[1]);
    while (isCons(l)) {
      const nx = D(l.a[1]);
      const m = e.mark();
      if (e.unify(a[0], l.a[0])) yield (isNil(nx) ? 'last' : undefined);
      e.undo(m);
      l = nx;
    }
    if (l.t === 'v') { // partial list: generate
      for (;;) { const h = Var(), t = Var(); const m = e.mark(); e.bind(l, cons(h, t)); if (e.unify(a[0], h)) yield; e.undo(m); const h2 = Var(); e.bind(l, cons(h2, t)); l = t; }
    }
  });
  det('memberchk/2', (a, e) => { let l = D(a[1]); while (isCons(l)) { const m = e.mark(); if (e.unify(a[0], l.a[0])) return true; e.undo(m); l = D(l.a[1]); } if (l.t === 'v') { return e.unify(l, cons(a[0], Var())); } return false; });
  nondet('append/3', function* (a, e) {
    const xs = listToArray(a[0]);
    if (xs) { if (e.unify(a[2], list(xs, a[1]))) yield 'last'; return; }
    { let x = D(a[0]); while (isCons(x)) x = D(x.a[1]); if (x.t !== 'v' && !P.isNil(x)) return; } // not a (partial) list
    { let z = D(a[2]); while (isCons(z)) z = D(z.a[1]); if (z.t !== 'v' && !P.isNil(z)) return; }
    // enumerate prefixes of a[2]
    let z = D(a[2]); const pre = [];
    for (;;) {
      const m = e.mark();
      if (e.unify(a[0], list(pre)) && e.unify(a[1], z)) yield (isNil(z) ? 'last' : undefined);
      e.undo(m);
      if (isCons(z)) { pre.push(z.a[0]); z = D(z.a[1]); continue; }
      if (z.t === 'v') { const h = Var(), t = Var(); e.bind(z, cons(h, t)); pre.push(h); z = t; continue; }
      return;
    }
  });
  det('append/2', (a, e) => { const ls = arr(a[0]); let r = NIL; const parts = ls.map(arr); const all = [].concat(...parts); return e.unify(a[1], list(all)); });
  nondet('length/2', function* (a, e) {
    let l = D(a[0]); let n = 0;
    while (isCons(l)) { n++; l = D(l.a[1]); }
    if (isNil(l)) { if (e.unify(a[1], Int(n))) yield 'last'; return; }
    if (l.t !== 'v') return;
    const N = D(a[1]);
    if (N.t === 'n') { if (N.v < n) return; const vs = []; for (let i = n; i < N.v; i++) vs.push(Var()); if (e.unify(l, list(vs))) yield 'last'; return; }
    for (let k = n; ; k++) { const vs = []; for (let i = n; i < k; i++) vs.push(Var()); const m = e.mark(); if (e.unify(l, list(vs)) && e.unify(N, Int(k))) yield; e.undo(m); }
  });
  det('reverse/2', (a, e) => e.unify(a[1], list(arr(a[0]).slice().reverse())));
  nondet('nth0/3', function* (a, e) { yield* nth(a, e, 0); });
  nondet('nth1/3', function* (a, e) { yield* nth(a, e, 1); });
  function* nth(a, e, base) {
    const i = D(a[0]); const l = arr(a[1]);
    if (i.t === 'n') { if (typeof i.v !== 'number') return; const k = i.v - base; if (k >= 0 && k < l.length && e.unify(a[2], l[k])) yield 'last'; return; }
    for (let k = 0; k < l.length; k++) { const m = e.mark(); if (e.unify(i, Int(k + base)) && e.unify(a[2], l[k])) yield; e.undo(m); }
  }
  nondet('last/2', function* (a, e) { const l = arr(a[0]); if (l.length && e.unify(a[1], l[l.length - 1])) yield 'last'; });
  det('msort/2', (a, e) => e.unify(a[1], list(arr(a[0]).slice().sort(compare))));
  det('sort/2', (a, e) => e.unify(a[1], list(sortUnique(arr(a[0])))));
  det('predsort/3', () => { throw new Error('predsort/3 is not supported'); });
  det('sort/4', (a, e) => {
    const k = D(a[0]).v; const ord = D(a[1]).n; let l = arr(a[2]).slice();
    const kf = x => { if (k === 0) return x; const t = D(x); if (t.t !== 'c' || t.a.length < k) throw new PlError(Cmp('error', [Cmp('type_error', [Atom('compound'), t]), Var()])); return t.a[k - 1]; };
    const cmp = (x, y) => compare(kf(x), kf(y));
    if (ord === '@<' || ord === '@=<') l.sort(cmp); else l.sort((x, y) => -cmp(x, y));
    if (ord === '@<' || ord === '@>') { const o = []; for (const x of l) if (!o.length || cmp(o[o.length - 1], x) !== 0) o.push(x); l = o; }
    return e.unify(a[3], list(l));
  });
  det('keysort/2', (a, e) => e.unify(a[1], list(arr(a[0]).slice().sort((x, y) => compare(D(x).a[0], D(y).a[0])))));
  // is_set(L): a proper list with no two elements == (SWI-Prolog's library(lists))
  det('is_set/1', (a) => { const l = listToArray(a[0]); if (!l) return false; for (let i = 0; i < l.length; i++) for (let j = i + 1; j < l.length; j++) if (compare(l[i], l[j]) === 0) return false; return true; });
  det('list_to_set/2', (a, e) => { const o = []; for (const x of arr(a[0])) if (!o.some(y => compare(x, y) === 0)) o.push(x); return e.unify(a[1], list(o)); });
  det('sum_list/2', (a, e) => { let s = Int(0); for (const x of arr(a[0])) s = evalArith(Cmp('+', [s, x])); return e.unify(a[1], s); });
  det('sumlist/2', B['sum_list/2'].fn);
  det('max_list/2', (a, e) => { const l = arr(a[0]).map(evalArith); if (!l.length) return false; return e.unify(a[1], l.reduce((m, x) => x.v > m.v ? x : m)); });
  det('min_list/2', (a, e) => { const l = arr(a[0]).map(evalArith); if (!l.length) return false; return e.unify(a[1], l.reduce((m, x) => x.v < m.v ? x : m)); });
  det('max_member/2', (a, e) => { const l = arr(a[1]); if (!l.length) return false; return e.unify(a[0], l.reduce((m, x) => compare(x, m) > 0 ? x : m)); });
  det('min_member/2', (a, e) => { const l = arr(a[1]); if (!l.length) return false; return e.unify(a[0], l.reduce((m, x) => compare(x, m) < 0 ? x : m)); });
  // the list is ground: its cells are marked so (copies and groundness checks of it are then O(1))
  det('numlist/3', (a, e) => { const lo = evalArith(a[0]).v, hi = evalArith(a[1]).v; let l = P.NIL; for (let i = hi; i >= lo; i--) l = { t: 'c', f: '.', a: [Int(i), l], gr: true }; return e.unify(a[2], l); });
  det('delete/3', (a, e) => { const o = arr(a[0]).filter(x => { const m = e.mark(); const r = e.unify(x, a[1]); e.undo(m); return !r; }); return e.unify(a[2], list(o)); });
  det('exclude_eq/3', () => false);
  det('subtract/3', (a, e) => { const b = arr(a[1]); const o = arr(a[0]).filter(x => !b.some(y => { const m = e.mark(); const r = e.unify(x, y); e.undo(m); return r; })); return e.unify(a[2], list(o)); });
  det('intersection/3', (a, e) => { const b = arr(a[1]); const o = arr(a[0]).filter(x => b.some(y => { const m = e.mark(); const r = e.unify(x, y); e.undo(m); return r; })); return e.unify(a[2], list(o)); });
  det('union/3', (a, e) => { const b = arr(a[1]); const o = arr(a[0]).filter(x => !b.some(y => { const m = e.mark(); const r = e.unify(x, y); e.undo(m); return r; })); return e.unify(a[2], list(o.concat(b))); });
  det('flatten/2', (a, e) => { const o = []; (function f(t) { t = D(t); if (isNil(t)) return; if (isCons(t)) { f(t.a[0]); f(t.a[1]); return; } o.push(t); })(a[0]); return e.unify(a[1], list(o)); });
  det('sumlist/3', () => false);
  det('exclude/3', null); delete B['exclude/3'];
  nondet('select/3', function* (a, e) {
    const l = listToArray(a[1]);
    if (l) { for (let i = 0; i < l.length; i++) { const m = e.mark(); if (e.unify(a[0], l[i]) && e.unify(a[2], list(l.slice(0, i).concat(l.slice(i + 1))))) yield; e.undo(m); } return; }
    const r = listToArray(a[2]); if (!r) throw instErr();
    for (let i = 0; i <= r.length; i++) { const m = e.mark(); if (e.unify(a[1], list(r.slice(0, i).concat([a[0]], r.slice(i))))) yield; e.undo(m); }
  });
  det('selectchk/3', (a, e) => { const l = arr(a[1]); for (let i = 0; i < l.length; i++) { const m = e.mark(); if (e.unify(a[0], l[i]) && e.unify(a[2], list(l.slice(0, i).concat(l.slice(i + 1))))) return true; e.undo(m); } return false; });
  nondet('permutation/2', function* (a, e) {
    const l = listToArray(a[0]) || (listToArray(a[1]) ? null : null);
    let src = l, other = a[1];
    if (!src) { src = arr(a[1]); other = a[0]; }
    const perm = function* (xs) { if (!xs.length) { yield []; return; } for (let i = 0; i < xs.length; i++) for (const r of perm(xs.slice(0, i).concat(xs.slice(i + 1)))) yield [xs[i]].concat(r); };
    for (const p of perm(src)) { const m = e.mark(); if (e.unify(other, list(p))) yield; e.undo(m); }
  });
  det('exclude_dummy/0', () => true); delete B['exclude_dummy/0'];
  det('pairs_keys_values/3', (a, e) => { const l = listToArray(a[0]); if (l) return e.unify(a[1], list(l.map(x => D(x).a[0]))) && e.unify(a[2], list(l.map(x => D(x).a[1]))); const ks = arr(a[1]), vs = arr(a[2]); return e.unify(a[0], list(ks.map((k, i) => Cmp('-', [k, vs[i]])))); });
  det('pairs_keys/2', (a, e) => e.unify(a[1], list(arr(a[0]).map(x => D(x).a[0]))));
  det('pairs_values/2', (a, e) => e.unify(a[1], list(arr(a[0]).map(x => D(x).a[1]))));
  det('sumlist/2', B['sum_list/2'].fn);
  det('max_min_dummy/0', () => true); delete B['max_min_dummy/0'];
  det('not_member/2', (a, e) => !arr(a[1]).some(y => compare(a[0], y) === 0));
  det('tab/2', () => true);

  // higher order (expand into goals; the converter specialises them instead)
  callb('maplist/2', a => mapGoal(a, 1)); callb('maplist/3', a => mapGoal(a, 2)); callb('maplist/4', a => mapGoal(a, 3)); callb('maplist/5', a => mapGoal(a, 4));
  function mapGoal(a, k) {
    const ls = a.slice(1);
    // build lists elementwise: unify each list with skeleton of same length
    const known = ls.map(l => listToArray(l)).find(x => x);
    if (!known) {
      // fall back to recursive definition
      return Cmp('$maplist_rec', [a[0], list(ls)]);
    }
    const n = known.length; const goals = []; const skels = [];
    for (let j = 0; j < k; j++) { const vs = []; for (let i = 0; i < n; i++) vs.push(Var()); skels.push(vs); goals.push(Cmp('=', [ls[j], list(vs)])); }
    for (let i = 0; i < n; i++) goals.push(Cmp('call', [a[0]].concat(skels.map(s => s[i]))));
    return conj(goals);
  }
  callb('$maplist_rec/2', a => {
    const ls = arr(a[1]); const hs = ls.map(() => Var()), ts = ls.map(() => Var());
    const nilCase = conj(ls.map(l => Cmp('=', [l, NIL])));
    const consCase = conj(ls.map((l, i) => Cmp('=', [l, cons(hs[i], ts[i])])).concat([Cmp('call', [a[0]].concat(hs)), Cmp('$maplist_rec', [a[0], list(ts)])]));
    return Cmp(';', [nilCase, consCase]);
  });
  callb('$foldl_rec/4', a => {
    const ls = arr(a[1]); const hs = ls.map(() => Var()), ts = ls.map(() => Var()), V1 = Var();
    const nilCase = conj(ls.map(l => Cmp('=', [l, NIL])).concat([Cmp('=', [a[2], a[3]])]));
    const consCase = conj(ls.map((l, i) => Cmp('=', [l, cons(hs[i], ts[i])])).concat([Cmp('call', [a[0]].concat(hs, [a[2], V1])), Cmp('$foldl_rec', [a[0], list(ts), V1, a[3]])]));
    return Cmp(';', [nilCase, consCase]);
  });
  callb('foldl/4', a => foldGoal(a, 1)); callb('foldl/5', a => foldGoal(a, 2)); callb('foldl/6', a => foldGoal(a, 3));
  function foldGoal(a, k) {
    // the lists may be partial (as SWI-Prolog's foldl walks them): a proper one sets the length
    const raw = a.slice(1, 1 + k), known = raw.map(l => listToArray(l)).find(x => x);
    const goals = []; let acc = a[1 + k];
    if (!known) return Cmp('$foldl_rec', [a[0], list(raw), acc, a[2 + k]]);
    const n = known.length;
    const ls = raw.map(l => { const x = listToArray(l); if (x && x.length === n) return x; const vs = []; for (let i = 0; i < n; i++) vs.push(Var()); goals.push(Cmp('=', [l, list(vs)])); return vs; });
    for (let i = 0; i < n; i++) { const nx = Var(); goals.push(Cmp('call', [a[0]].concat(ls.map(l => l[i]), [acc, nx]))); acc = nx; }
    goals.push(Cmp('=', [acc, a[2 + k]]));
    return conj(goals);
  }
  callb('include/3', a => { const l = arr(a[1]); const R = a[2]; const outs = l.map(() => Var()); const goals = l.map((x, i) => Cmp(';', [Cmp('->', [Cmp('call', [a[0], x]), Cmp('=', [outs[i], list([x])])]), Cmp('=', [outs[i], NIL])])); goals.push(Cmp('append', [list(outs), R])); return conj(goals); });
  callb('exclude/3', a => { const l = arr(a[1]); const R = a[2]; const outs = l.map(() => Var()); const goals = l.map((x, i) => Cmp(';', [Cmp('->', [Cmp('call', [a[0], x]), Cmp('=', [outs[i], NIL])]), Cmp('=', [outs[i], list([x])])])); goals.push(Cmp('append', [list(outs), R])); return conj(goals); });
  callb('partition/4', a => { const l = arr(a[1]); const I = l.map(() => Var()), X = l.map(() => Var()); const goals = l.map((x, i) => Cmp(';', [Cmp('->', [Cmp('call', [a[0], x]), Cmp(',', [Cmp('=', [I[i], list([x])]), Cmp('=', [X[i], NIL])])]), Cmp(',', [Cmp('=', [I[i], NIL]), Cmp('=', [X[i], list([x])])])])); goals.push(Cmp('append', [list(I), a[2]]), Cmp('append', [list(X), a[3]])); return conj(goals); });
  // yall lambdas: copy the lambda (Free/Lambda keeps Free shared), bind parameters, call the body
  for (let n = 2; n <= 9; n++) callb('>>/' + n, a => {
    let lam = Cmp('>>', [a[0], a[1]]); const extra = a.slice(2);
    let free = null, ps = D(a[0]);
    if (ps.t === 'c' && ps.f === '/' && ps.a.length === 2) free = ps.a[0];
    const m = new Map(); if (free) for (const v of termVars(free)) m.set(v, v);
    const c = copy(lam, m); let params = D(c.a[0]); if (params.t === 'c' && params.f === '/') params = D(params.a[1]);
    const pl = listToArray(params) || [];
    const goals = [];
    pl.forEach((p, i) => { if (i < extra.length) goals.push(Cmp('=', [p, extra[i]])); });
    let body = c.a[1];
    if (extra.length > pl.length) body = Cmp('call', [body].concat(extra.slice(pl.length)));
    goals.push(body);
    return conj(goals);
  });
  callb('phrase/2', a => Cmp('call', [a[0], a[1], NIL]));
  callb('phrase/3', a => Cmp('call', [a[0], a[1], a[2]]));
  function conj(gs) { if (!gs.length) return P.TRUE; let r = gs[gs.length - 1]; for (let i = gs.length - 2; i >= 0; i--) r = Cmp(',', [gs[i], r]); return r; }

  // database
  det('assert/1', (a, e) => { e.prog.add(copy(a[0])); return true; });
  det('assertz/1', B['assert/1'].fn);
  det('asserta/1', (a, e) => { e.prog.add(copy(a[0]), null, false); return true; });
  nondet('retract/1', function* (a, e) {
    let t = D(a[0]); let h = t, b = P.TRUE; if (t.t === 'c' && t.f === ':-') { h = D(t.a[0]); b = t.a[1]; }
    const cls = e.prog.preds.get(P.key(h)); if (!cls) return;
    for (const cl of cls.slice()) { const m = e.mark(); const mp = new Map(); if (e.unify(h, copy(cl.head, mp)) && e.unify(b, copy(cl.body, mp))) { const i = cls.indexOf(cl); if (i >= 0) cls.splice(i, 1); yield; } e.undo(m); }
  });
  det('retractall/1', (a, e) => { const h = D(a[0]); const k = P.key(h); const cls = e.prog.preds.get(k); if (!cls) { e.prog.preds.set(k, []); e.prog.dynamic.add(k); return true; } for (const cl of cls.slice()) { const m = e.mark(); if (e.unify(h, copy(cl.head))) cls.splice(cls.indexOf(cl), 1); e.undo(m); } return true; });
  det('nb_setval/2', (a, e) => { e.globals.set(textOf(a[0]), copy(a[1])); return true; });
  det('b_setval/2', B['nb_setval/2'].fn);
  det('nb_getval/2', (a, e) => { const v = e.globals.get(textOf(a[0])); if (!v) throw new PlError(Cmp('error', [Cmp('existence_error', [Atom('variable'), a[0]]), Var()])); return e.unify(a[1], v); });
  det('b_getval/2', B['nb_getval/2'].fn);
  det('garbage_collect/0', () => true);
  // statistics/2 as in SWI-Prolog: cputime and process_cputime/real_time/epoch/inferences are numbers,
  // runtime/walltime/system_time are [Total, SinceLast] in milliseconds
  det('statistics/2', (a, e) => {
    const k = P.textOf(a[0]), ms = P.now(); e.statLast = e.statLast || {};
    if (k === 'cputime' || k === 'process_cputime') return e.unify(a[1], Num(ms / 1000, true));
    if (k === 'inferences') return e.unify(a[1], Int(e.steps));
    if (k === 'epoch') return e.unify(a[1], Num(Date.now() / 1000 - ms / 1000, true));
    if (k === 'real_time') return e.unify(a[1], Int(Math.floor(Date.now() / 1000)));
    const last = e.statLast[k] || 0; e.statLast[k] = ms;
    return e.unify(a[1], list([Int(Math.round(ms)), Int(Math.round(ms - last))]));
  });
  det('get_time/1', (a, e) => e.unify(a[0], Num(Date.now() / 1000, true)));
  det('random/1', (a, e) => e.unify(a[0], Num(Math.random(), true)));
  det('random_between/3', (a, e) => { const lo = evalArith(a[0]).v, hi = evalArith(a[1]).v; return e.unify(a[2], Int(lo + Math.floor(Math.random() * (hi - lo + 1)))); });
  det('succ_or_zero/1', () => true); delete B['succ_or_zero/1'];
  det('ensure_loaded/1', () => true);
  det('use_module/1', () => true);
  det('use_module/2', () => true);
  det('set_prolog_flag/2', () => true);
  det('style_check/1', () => true);
  det('discontiguous/1', () => true);
  det('dynamic/1', (a, e) => { for (const s of P.commaList(a[0])) { const sd = D(s); const k = P.name(sd.a[0]) + '/' + D(sd.a[1]).v; e.prog.dynamic.add(k); if (!e.prog.preds.has(k)) e.prog.preds.set(k, []); } return true; });
  det('tabling_dummy/0', () => true); delete B['tabling_dummy/0'];

  P.builtins = B;
  P.conj = conj;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* swi.js - SWI-Prolog compatibility for the reference engine, so that ordinary SWI-Prolog programs
   (LucianOS's among them) run unchanged on the interpreter (src/interp.js):

   - dicts (read by core.js as dict(Tag, [K-V, ...])): is_dict, get_dict, put_dict, del_dict,
     dict_pairs, dict_create
   - JSON as library(http/json) reads and writes it: atom_json_dict, atom_json_term, json_read_dict,
     json_write_dict, json_write, json_read
   - streams and files through the engine's io: open, close, read_line_to_string/codes, read_term,
     read, read_string, write/2, format/3 to streams, user_input/user_output/user_error,
     read_file_to_string, read_file_to_terms, exists_file, absolute_file_name, ...
   - modules: module/2 and use_module/1,2 directives are read (library modules are built in, file
     modules are loaded by the interpreter); Module:Goal calls Goal
   - clause/2, current_prolog_flag/2 (argv), print_message/2, setup_call_cleanup/3 and a few more

   The engine's io object answers for the file system and the process; the interpreter makes it. */
(function (P) {
  'use strict';
  const { Atom, Num, Int, Str, Var, Cmp, NIL, list, deref: D, listToArray, copy, show, compare, isGround } = P;
  const B = P.builtins;
  const det = (k, fn) => { B[k] = { fn }; };
  const nondet = (k, fn) => { B[k] = { fn, nondet: true }; };
  const callb = (k, fn) => { B[k] = { fn, call: true }; };
  const err = (formal) => new P.PlError(Cmp('error', [formal, Var()]));
  const domErr = (d, c) => err(Cmp('domain_error', [Atom(d), c]));
  const existErr = (k, c) => err(Cmp('existence_error', [Atom(k), c]));
  const permErr = (a, t, c) => err(Cmp('permission_error', [Atom(a), Atom(t), c]));
  const textOf = (t) => P.textOf(t);
  const SWI = (t, quoted) => show(t, { quoted, swi: !!P.SWI_WRITE });

  // ---------------------------------------------------------------- dicts
  const isDict = (t) => P.dictPairs(t) !== null;
  const dictOf = (t) => { const ps = P.dictPairs(t); if (!ps) { if (D(t).t === 'v') throw P.instErr(); throw P.typeError('dict', t); } return ps; };
  const mk = (tag, ps) => P.mkDict(tag, ps);
  det('is_dict/1', (a) => isDict(a[0]));
  det('is_dict/2', (a, e) => isDict(a[0]) && e.unify(a[1], D(a[0]).a[0]));
  nondet('get_dict/3', function* (a, e) {
    const ps = dictOf(a[1]), k = D(a[0]);
    if (k.t !== 'v') { const p = ps.find(([kk]) => compare(kk, k) === 0); if (p && e.unify(a[2], p[1])) yield 'last'; return; }
    for (const [kk, v] of ps) { const m = e.mark(); if (e.unify(k, kk) && e.unify(a[2], v)) yield; e.undo(m); }
  });
  det('put_dict/4', (a, e) => { const ps = dictOf(a[1]).filter(([k]) => compare(k, D(a[0])) !== 0); ps.push([D(a[0]), a[2]]); return e.unify(a[3], mk(D(a[1]).a[0], ps)); });
  det('put_dict/3', (a, e) => {
    const nw = isDict(a[0]) ? dictOf(a[0]) : (listToArray(a[0]) || []).map((x) => { x = D(x); return [D(x.a[0]), x.a[1]]; });
    const ps = dictOf(a[1]).filter(([k]) => !nw.some(([k2]) => compare(k, k2) === 0)).concat(nw);
    return e.unify(a[2], mk(D(a[1]).a[0], ps));
  });
  det('del_dict/4', (a, e) => { const ps = dictOf(a[1]); const i = ps.findIndex(([k]) => compare(k, D(a[0])) === 0); if (i < 0 || !e.unify(a[2], ps[i][1])) return false; ps.splice(i, 1); return e.unify(a[3], mk(D(a[1]).a[0], ps)); });
  det('dict_pairs/3', (a, e) => {
    const d = D(a[0]);
    if (d.t !== 'v') { const ps = dictOf(d); return e.unify(a[1], d.a[0]) && e.unify(a[2], list(ps.map(([k, v]) => Cmp('-', [k, v])))); }
    const ps = (listToArray(a[2]) || []).map((x) => { x = D(x); return [D(x.a[0]), x.a[1]]; });
    return e.unify(d, mk(a[1], ps));
  });
  det('dict_create/3', (a, e) => { const ps = (listToArray(a[2]) || []).map((x) => { x = D(x); return [D(x.a[0]), x.a[1]]; }); return e.unify(a[0], mk(a[1], ps)); });
  det('get_dict/5', (a, e) => { const ps = dictOf(a[1]); const i = ps.findIndex(([k]) => compare(k, D(a[0])) === 0); if (i < 0 || !e.unify(a[2], ps[i][1])) return false; ps[i] = [ps[i][0], a[3]]; return e.unify(a[4], mk(D(a[1]).a[0], ps)); });

  // ---------------------------------------------------------------- JSON
  // value_string_as: strings by default (as SWI-Prolog's atom_json_dict); true/false/null as atoms
  function parseJSON(text, dicts, opts = {}) {
    let v; try { v = JSON.parse(text); } catch (x) { throw err(Cmp('syntax_error', [Atom('json(' + x.message.replace(/[^a-z0-9 ]/gi, '').slice(0, 60) + ')')])); }
    const strAs = opts.strAs || (dicts ? 'string' : 'atom');
    const tr = (x) => {
      if (x === null) return Atom('null'); if (x === true) return Atom('true'); if (x === false) return Atom('false');
      if (typeof x === 'number') return Number.isInteger(x) ? Int(x) : Num(x, true);
      if (typeof x === 'string') return strAs === 'atom' ? Atom(x) : Str(x);
      if (Array.isArray(x)) return list(x.map(tr));
      if (dicts) return mk(opts.tag || Var(), Object.keys(x).map((k) => [/^-?\d+$/.test(k) && Number.isSafeInteger(+k) ? Int(+k) : Atom(k), tr(x[k])]));
      return Cmp('json', [list(Object.keys(x).map((k) => Cmp('=', [Atom(k), tr(x[k])])))]);
    };
    return tr(v);
  }
  function toJSONValue(t) {
    t = D(t);
    switch (t.t) {
      case 'v': throw P.instErr();
      case 'n': return typeof t.v === 'bigint' ? { raw: t.v.toString() } : t.v;
      case 's': return t.v;
      case 'a': return t.n === 'null' ? null : t.n === 'true' ? true : t.n === 'false' ? false : t.n === '[]' ? [] : t.n;
      case 'c': {
        if (t.f === 'dict' && isDict(t)) { const o = {}; for (const [k, v] of P.dictPairs(t)) o[textOf(k)] = toJSONValue(v); return o; }
        if (t.f === 'json' && t.a.length === 1) { const o = {}; for (const x of listToArray(t.a[0]) || []) { const p = D(x); o[textOf(p.a[0])] = toJSONValue(p.a[1]); } return o; }
        if (t.f === '.' && t.a.length === 2) { const l = listToArray(t); if (l) return l.map(toJSONValue); }
        if (t.f === '@' && t.a.length === 1) return toJSONValue(t.a[0]);
        if (t.f === 'string' && t.a.length === 1) return textOf(t.a[0]);
        throw P.typeError('json_term', t);
      }
    }
  }
  // as SWI-Prolog writes JSON: width(0) on one line ({"a":1, "b":2}), otherwise laid out with 2 spaces
  function writeJSON(v, pretty, ind = 0) {
    const q = (s) => JSON.stringify(s);
    if (v && typeof v === 'object' && 'raw' in v && Object.keys(v).length === 1) return v.raw;
    if (Array.isArray(v)) {
      if (!v.length) return '[]';
      if (!pretty) return '[' + v.map((x) => writeJSON(x, false)).join(', ') + ']';
      const simple = v.every((x) => x === null || typeof x !== 'object');
      if (simple) { const one = '[' + v.map((x) => writeJSON(x, false)).join(', ') + ']'; if (one.length + ind < 72) return one; }
      return '[\n' + v.map((x) => ' '.repeat(ind + 2) + writeJSON(x, true, ind + 2)).join(',\n') + '\n' + ' '.repeat(ind) + ']';
    }
    if (v && typeof v === 'object') {
      const ks = Object.keys(v); if (!ks.length) return '{}';
      if (!pretty) return '{' + ks.map((k) => q(k) + ':' + writeJSON(v[k], false)).join(', ') + '}';
      const one = '{' + ks.map((k) => q(k) + ':' + writeJSON(v[k], false)).join(', ') + '}';
      if (one.length + ind < 72 && !one.includes('{', 1)) return one;
      return '{\n' + ks.map((k) => ' '.repeat(ind + 2) + q(k) + ':' + writeJSON(v[k], true, ind + 2)).join(',\n') + '\n' + ' '.repeat(ind) + '}';
    }
    if (typeof v === 'number') return Number.isInteger(v) ? String(v) : String(v).includes('e') || String(v).includes('.') ? String(v) : String(v) + '.0';
    return q(v);
  }
  const jsonOpts = (o) => { const r = { pretty: true, strAs: null, tag: null }; for (const x of listToArray(o) || []) { const t = D(x); if (t.t === 'c' && t.a.length === 1) { const v = D(t.a[0]); if (t.f === 'width' && v.t === 'n' && v.v === 0) r.pretty = false; if (t.f === 'value_string_as') r.strAs = v.n; if (t.f === 'tag') r.tag = v; } } return r; };
  det('atom_json_dict/3', (a, e) => {
    const t = D(a[0]), o = jsonOpts(a[2]);
    if (t.t !== 'v') return e.unify(a[1], parseJSON(textOf(t), true, o));
    return e.unify(t, Atom(writeJSON(toJSONValue(a[1]), o.pretty)));
  });
  det('atom_json_term/3', (a, e) => {
    const t = D(a[0]), o = jsonOpts(a[2]);
    if (t.t !== 'v') return e.unify(a[1], parseJSON(textOf(t), false, o));
    return e.unify(t, Atom(writeJSON(toJSONValue(a[1]), o.pretty)));
  });
  det('json_read_dict/2', (a, e) => e.unify(a[1], parseJSON(readAll(e, a[0]), true)));
  det('json_read_dict/3', (a, e) => e.unify(a[1], parseJSON(readAll(e, a[0]), true, jsonOpts(a[2]))));
  det('json_read/2', (a, e) => e.unify(a[1], parseJSON(readAll(e, a[0]), false)));
  det('json_write_dict/2', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), true)); return true; });
  det('json_write_dict/3', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), jsonOpts(a[2]).pretty)); return true; });
  det('json_write/2', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), true)); return true; });
  det('json_write/3', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), jsonOpts(a[2]).pretty)); return true; });

  // ---------------------------------------------------------------- files and streams
  const io = (e) => e.io || P.defaultIO || null;
  // an io call that fails (no such file, no permission) raises the Prolog error SWI-Prolog would
  const ioDo = (what, path, f) => { try { return f(); } catch (x) { if (x instanceof P.PlError) throw x; if (x && x.code === 'ENOENT') throw existErr('file', Atom(path)); throw permErr(what, 'file', Atom(path)); } };
  const resolvePath = (e, p) => { const cwd = (io(e) && io(e).cwd) || ''; return P.joinPath(cwd, p); };
  P.joinPath = (cwd, p) => {
    if (!p) return cwd || '.';
    if (/^([A-Za-z]:)?[\\/]/.test(p) || !cwd || cwd === '.') return normal(p);
    return normal(cwd.replace(/[\\/]+$/, '') + '/' + p);
  };
  function normal(p) { const abs = p.startsWith('/'); const out = []; for (const s of p.split(/[\\/]+/)) { if (!s || s === '.') continue; if (s === '..' && out.length && out[out.length - 1] !== '..') out.pop(); else out.push(s); } const r = (abs ? '/' : '') + out.join('/'); return r || (abs ? '/' : '.'); }
  const fileText = (e, path) => { const x = io(e); const t = x && x.readFile ? x.readFile(path) : null; if (t == null) throw existErr('source_sink', Atom(path)); return t; };
  function streamOf(e, t, mode) {
    t = D(t);
    if (t.t === 'v') throw P.instErr();
    if (t.t === 'a') {
      if (t.n === 'user_output' || t.n === 'current_output') return { id: 'out', mode: 'write' };
      if (t.n === 'user_error') return { id: 'err', mode: 'write' };
      if (t.n === 'user_input' || t.n === 'current_input') {
        // standard input is read as it is needed (io.readStdin() gives the next piece, or null at its end)
        if (!e.streams.has('in')) { const x = io(e) || {}; e.streams.set('in', { id: 'in', mode: 'read', text: typeof x.stdin === 'string' ? x.stdin : '', pos: 0, line: 1, more: x.readStdin ? () => x.readStdin() : null }); }
        return e.streams.get('in');
      }
      for (const s of e.streams.values()) if (s.alias === t.n) return s;
    }
    if (t.t === 'c' && t.f === '$stream' && t.a.length === 1) { const s = e.streams.get(D(t.a[0]).v); if (s) return s; }
    throw existErr('stream', t);
  }
  function put(e, st, text) {
    const s = st && st.mode ? st : streamOf(e, st);
    if (s.mode !== 'write' && s.mode !== 'append') throw permErr('output', 'stream', Atom(String(s.id)));
    if (s.id === 'out') e.write(text); else if (s.id === 'err') e.writeErr(text); else if (s.sink) s.sink.push(text); else s.buf += text;
  }
  P.streamPut = put;
  function pull(s) { if (!s.more) return false; const t = s.more(); if (t == null) { s.more = null; return false; } s.text += t; return true; }
  function readAll(e, st) { const s = streamOf(e, st); while (pull(s)); const t = s.text.slice(s.pos); s.pos = s.text.length; return t; }
  function readLine(e, st) {
    const s = streamOf(e, st);
    while (s.text.indexOf('\n', s.pos) < 0 && pull(s));
    if (s.pos >= s.text.length) return null;
    let i = s.text.indexOf('\n', s.pos); if (i < 0) i = s.text.length;
    let line = s.text.slice(s.pos, i); s.pos = Math.min(s.text.length, i + 1); s.line++;
    if (line.endsWith('\r')) line = line.slice(0, -1);
    return line;
  }
  det('open/3', (a, e) => openStream(a, e, NIL));
  det('open/4', (a, e) => openStream(a, e, a[3]));
  function openStream(a, e, opts) {
    const path = resolvePath(e, textOf(a[0])), mode = textOf(a[1]);
    const id = ++e.streamSeq;
    let s;
    if (mode === 'read') s = { id, mode, path, text: fileText(e, path), pos: 0, line: 1 };
    else if (mode === 'write' || mode === 'append') { const x = io(e); if (!x || !x.writeFile) throw permErr('open', 'source_sink', Atom(path)); s = { id, mode, path, buf: '' }; }
    else throw domErr('io_mode', a[1]);
    for (const o of listToArray(opts) || []) { const t = D(o); if (t.t === 'c' && t.f === 'alias') s.alias = textOf(t.a[0]); }
    e.streams.set(id, s);
    return e.unify(a[2], Cmp('$stream', [Int(id)]));
  }
  function closeStream(e, s) {
    if (!s || s.closed || typeof s.id !== 'number') return;
    s.closed = true; e.streams.delete(s.id);
    if (s.mode === 'write' || s.mode === 'append') ioDo('write', s.path, () => io(e).writeFile(s.path, s.buf, s.mode === 'append'));
  }
  P.closeStreams = (e) => { for (const s of [...e.streams.values()]) closeStream(e, s); };
  det('close/1', (a, e) => { closeStream(e, streamOf(e, a[0])); return true; });
  det('close/2', (a, e) => { closeStream(e, streamOf(e, a[0])); return true; });
  det('read_line_to_string/2', (a, e) => { const l = readLine(e, a[0]); return e.unify(a[1], l === null ? Atom('end_of_file') : Str(l)); });
  det('read_line_to_codes/2', (a, e) => { const l = readLine(e, a[0]); return e.unify(a[1], l === null ? Int(-1) : P.codesList(l)); });
  det('read_string/3', (a, e) => { const t = readAll(e, a[0]); return e.unify(a[1], Int(t.length)) && e.unify(a[2], Str(t)); });
  det('read_string/5', (a, e) => {
    // read_string(+Stream, +SepChars, +PadChars, -Sep, -String)
    const s = streamOf(e, a[0]); const seps = textOf(a[1]), pad = textOf(a[2]);
    if (s.pos >= s.text.length) return e.unify(a[3], Int(-1)) && e.unify(a[4], Str(''));
    let i = s.pos; while (i < s.text.length && !seps.includes(s.text[i])) i++;
    let str = s.text.slice(s.pos, i); const sep = i < s.text.length ? Int(s.text.charCodeAt(i)) : Int(-1); s.pos = Math.min(s.text.length, i + 1);
    let lo = 0, hi = str.length; while (lo < hi && pad.includes(str[lo])) lo++; while (hi > lo && pad.includes(str[hi - 1])) hi--;
    return e.unify(a[3], sep) && e.unify(a[4], Str(str.slice(lo, hi)));
  });
  function readTermFrom(e, st) {
    const s = streamOf(e, st);
    // the next clause: up to a full stop followed by layout or the end
    while (P.nextClauseText(s.text.slice(s.pos)) === s.text.slice(s.pos) && pull(s));
    const rest = s.text.slice(s.pos);
    const toks = P.nextClauseText(rest);
    if (toks === null) { s.pos = s.text.length; return { term: Atom('end_of_file'), vars: [] }; }
    s.pos += toks.length;
    return P.readTerm(toks);
  }
  det('read_term/2', (a, e) => { const r = readTermFrom(e, Atom('user_input')); bindReadOpts(e, a[1], r); return e.unify(a[0], r.term); });
  det('read_term/3', (a, e) => { const r = readTermFrom(e, a[0]); bindReadOpts(e, a[2], r); return e.unify(a[1], r.term); });
  det('read/1', (a, e) => e.unify(a[0], readTermFrom(e, Atom('user_input')).term));
  det('read/2', (a, e) => e.unify(a[1], readTermFrom(e, a[0]).term));
  function bindReadOpts(e, opts, r) {
    for (const o of listToArray(opts) || []) {
      const t = D(o); if (t.t !== 'c' || t.a.length !== 1) continue;
      if (t.f === 'variable_names') e.unify(t.a[0], list((r.vars || []).map(([n, v]) => Cmp('=', [Atom(n), v]))));
      if (t.f === 'variables') e.unify(t.a[0], list((r.vars || []).map(([, v]) => v)));
      // the named variables that appear once (not those starting with _), as Name = Var
      if (t.f === 'singletons') {
        const counts = new Map(); const st = [r.term];
        while (st.length) { const x = D(st.pop()); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') for (const y of x.a) st.push(y); }
        e.unify(t.a[0], list((r.vars || []).filter(([n, v]) => !n.startsWith('_') && counts.get(D(v)) === 1).map(([n, v]) => Cmp('=', [Atom(n), v]))));
      }
    }
  }
  // the text of the next clause in src (through its full stop), or null at the end
  P.nextClauseText = (src) => {
    let i = 0, n = src.length;
    const skipLayout = () => { for (;;) { while (i < n && /\s/.test(src[i])) i++; if (src[i] === '%') { while (i < n && src[i] !== '\n') i++; continue; } if (src[i] === '/' && src[i + 1] === '*') { const j = src.indexOf('*/', i + 2); i = j < 0 ? n : j + 2; continue; } break; } };
    skipLayout(); if (i >= n) return null;
    while (i < n) {
      const c = src[i];
      if (c === '%') { while (i < n && src[i] !== '\n') i++; continue; }
      if (c === '/' && src[i + 1] === '*') { const j = src.indexOf('*/', i + 2); i = j < 0 ? n : j + 2; continue; }
      if (c === '"' || c === "'" || c === '`') { i++; while (i < n && src[i] !== c) { if (src[i] === '\\') i++; i++; } i++; continue; }
      if (c === '0' && src[i + 1] === "'") { i += src[i + 2] === '\\' ? 4 : 3; continue; }
      if (c === '.' && (i + 1 >= n || /\s|%/.test(src[i + 1])) && !/[#$&*+\-./:<=>?@^~\\]/.test(src[i - 1] || ' ')) return src.slice(0, i + 1);
      i++;
    }
    return src;
  };
  det('read_file_to_string/3', (a, e) => e.unify(a[1], Str(fileText(e, resolvePath(e, textOf(a[0]))))));
  det('read_file_to_codes/3', (a, e) => e.unify(a[1], P.codesList(fileText(e, resolvePath(e, textOf(a[0]))))));
  det('read_file_to_terms/3', (a, e) => { const cls = P.readProgram(fileText(e, resolvePath(e, textOf(a[0])))); return e.unify(a[1], list(cls.map((c) => c.term))); });
  det('exists_file/1', (a, e) => { const x = io(e); return !!(x && x.stat && x.stat(resolvePath(e, textOf(a[0]))) === 'file'); });
  det('exists_directory/1', (a, e) => { const x = io(e); return !!(x && x.stat && x.stat(resolvePath(e, textOf(a[0]))) === 'dir'); });
  det('directory_files/2', (a, e) => { const x = io(e); const l = x && x.list ? x.list(resolvePath(e, textOf(a[0]))) : null; if (!l) throw existErr('directory', a[0]); return e.unify(a[1], list(['.', '..'].concat(l).map((n) => Atom(n)))); });
  const absOf = (e, p) => { const x = io(e); const r = resolvePath(e, p); if (r.startsWith('/') || /^[A-Za-z]:/.test(r)) return r; return x && x.root ? P.joinPath(x.root, r) : r; };
  det('absolute_file_name/2', (a, e) => e.unify(a[1], Atom(absOf(e, fileSpec(a[0])))));
  det('absolute_file_name/3', (a, e) => {
    let p = fileSpec(a[0]); const x = io(e);
    for (const o of listToArray(a[2]) || []) { const t = D(o); if (t.t === 'c' && t.f === 'extensions') { for (const ext of listToArray(t.a[0]) || []) { const ex = textOf(ext); const c = ex ? p + '.' + ex : p; if (x && x.stat && x.stat(resolvePath(e, c))) { p = c; break; } } } }
    return e.unify(a[1], Atom(absOf(e, p)));
  });
  const fileSpec = (t) => { t = D(t); if (t.t === 'c' && t.a.length === 1 && t.f !== '/') return textOf(t.a[0]); if (t.t === 'c' && t.f === '/' && t.a.length === 2) return fileSpec(t.a[0]) + '/' + fileSpec(t.a[1]); return textOf(t); };
  det('file_directory_name/2', (a, e) => { const p = textOf(a[0]).replace(/\/+$/, ''); const i = p.lastIndexOf('/'); return e.unify(a[1], Atom(i < 0 ? '.' : i === 0 ? '/' : p.slice(0, i))); });
  det('file_base_name/2', (a, e) => { const p = textOf(a[0]); return e.unify(a[1], Atom(p.slice(p.lastIndexOf('/') + 1))); });
  det('file_name_extension/3', (a, e) => {
    const f = D(a[2]);
    if (f.t !== 'v') { const s = textOf(f); const b = s.slice(s.lastIndexOf('/') + 1); const i = b.lastIndexOf('.'); if (i <= 0) return e.unify(a[0], Atom(s)) && e.unify(a[1], Atom('')); return e.unify(a[0], Atom(s.slice(0, s.length - b.length + i))) && e.unify(a[1], Atom(b.slice(i + 1))); }
    const ext = textOf(a[1]).replace(/^\./, ''); return e.unify(f, Atom(ext ? textOf(a[0]) + '.' + ext : textOf(a[0])));
  });
  det('delete_file/1', (a, e) => { const x = io(e); if (!x || !x.deleteFile) throw permErr('delete', 'file', a[0]); const p = resolvePath(e, textOf(a[0])); ioDo('delete', p, () => x.deleteFile(p)); return true; });
  det('make_directory/1', (a, e) => { const x = io(e); if (!x || !x.mkdir) throw permErr('create', 'directory', a[0]); const p = resolvePath(e, textOf(a[0])); ioDo('create', p, () => x.mkdir(p)); return true; });
  det('working_directory/2', (a, e) => { const x = io(e) || {}; const cur = Atom(((x.cwd || '.') + '/').replace(/\/+$/, '/')); if (!e.unify(a[0], cur)) return false; const n = D(a[1]); if (n.t !== 'v' && x) x.cwd = resolvePath(e, textOf(n)); return true; });
  det('getenv/2', (a, e) => { const x = io(e); const v = x && x.env ? x.env[textOf(a[0])] : undefined; return v != null && e.unify(a[1], Atom(v)); });
  det('shell/1', (a, e) => { const x = io(e); if (!x || !x.shell) throw permErr('execute', 'shell', a[0]); return x.shell(textOf(a[0])) === 0; });
  det('shell/2', (a, e) => { const x = io(e); if (!x || !x.shell) throw permErr('execute', 'shell', a[0]); return e.unify(a[1], Int(x.shell(textOf(a[0])))); });

  // output to streams; as SWI-Prolog lays terms out
  det('write/1', (a, e) => { e.write(SWI(a[0], false)); return true; });
  det('print/1', (a, e) => { e.write(SWI(a[0], true)); return true; });
  det('writeln/1', (a, e) => { e.write(SWI(a[0], false) + '\n'); return true; });
  det('writeq/1', (a, e) => { e.write(SWI(a[0], true)); return true; });
  det('write_canonical/1', (a, e) => { e.write(show(a[0], { quoted: true, ignoreOps: true, swi: !!P.SWI_WRITE })); return true; });
  det('write_term/2', (a, e) => { e.write(show(a[0], { quoted: wtQuoted(a[1]), swi: !!P.SWI_WRITE, nextArg: wtNext(a[1]) })); return true; });
  det('write_term/3', (a, e) => { put(e, a[0], show(a[1], { quoted: wtQuoted(a[2]), swi: !!P.SWI_WRITE, nextArg: wtNext(a[2]) })); return true; });
  const wtNext = (o) => (listToArray(o) || []).some((x) => { x = D(x); return x.t === 'c' && x.f === 'spacing' && D(x.a[0]).n === 'next_argument'; });
  const wtQuoted = (o) => (listToArray(o) || []).some((x) => { x = D(x); return x.t === 'c' && x.f === 'quoted' && D(x.a[0]).n === 'true'; });
  det('write/2', (a, e) => { put(e, a[0], SWI(a[1], false)); return true; });
  det('writeln/2', (a, e) => { put(e, a[0], SWI(a[1], false) + '\n'); return true; });
  det('writeq/2', (a, e) => { put(e, a[0], SWI(a[1], true)); return true; });
  det('print/2', (a, e) => { put(e, a[0], SWI(a[1], true)); return true; });
  det('nl/1', (a, e) => { put(e, a[0], '\n'); return true; });
  det('tab/2', (a, e) => { put(e, a[0], ' '.repeat(Number(P.evalArith(a[1]).v))); return true; });
  det('put_char/2', (a, e) => { put(e, a[0], textOf(a[1])); return true; });
  det('flush_output/1', () => true);
  det('format/3', (a, e) => {
    const s = D(a[0]); const txt = P.format(a[1], a[2]);
    if (s.t === 'c' && s.a.length === 1 && ['atom', 'string', 'codes', 'chars'].includes(s.f)) {
      const k = s.f; return e.unify(s.a[0], k === 'atom' ? Atom(txt) : k === 'string' ? Str(txt) : k === 'codes' ? P.codesList(txt) : P.charsList(txt));
    }
    put(e, s, txt); return true;
  });
  det('current_output/1', (a, e) => e.unify(a[0], Atom('user_output')));
  det('current_input/1', (a, e) => e.unify(a[0], Atom('user_input')));
  det('set_stream/2', () => true);
  det('prompt/2', (a, e) => e.unify(a[0], Atom('|: ')));
  det('at_end_of_stream/0', (a, e) => { const s = streamOf(e, Atom('user_input')); if (s.pos >= s.text.length) pull(s); return s.pos >= s.text.length; });
  det('at_end_of_stream/1', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return s.pos >= s.text.length; });
  det('get_char/1', (a, e) => { const s = streamOf(e, Atom('user_input')); if (s.pos >= s.text.length) pull(s); return e.unify(a[0], s.pos < s.text.length ? Atom(s.text[s.pos++]) : Atom('end_of_file')); });
  det('get_char/2', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return e.unify(a[1], s.pos < s.text.length ? Atom(s.text[s.pos++]) : Atom('end_of_file')); });
  det('peek_char/2', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return e.unify(a[1], s.pos < s.text.length ? Atom(s.text[s.pos]) : Atom('end_of_file')); });
  det('get_code/2', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return e.unify(a[1], Int(s.pos < s.text.length ? s.text.charCodeAt(s.pos++) : -1)); });

  // messages, as SWI-Prolog prints an uncaught error or a warning (to user_error)
  det('print_message/2', (a, e) => {
    const kind = textOf(a[0]); if (kind === 'silent' || kind === 'informational') return true;
    e.writeErr((kind === 'error' ? 'ERROR: ' : kind === 'warning' ? 'Warning: ' : '') + messageText(a[1]) + '\n'); return true;
  });
  function messageText(t) {
    t = D(t);
    if (t.t === 'c' && t.f === 'error' && t.a.length === 2) {
      const f = D(t.a[0]);
      if (f.t === 'c' && f.f === 'existence_error' && D(f.a[0]).n === 'procedure') return 'Unknown procedure: ' + SWI(f.a[1], true);
      if (f.t === 'c' && f.f === 'type_error') return 'Type error: `' + SWI(f.a[0], false) + "' expected, found `" + SWI(f.a[1], true) + "'";
      if (f.t === 'a' && f.n === 'instantiation_error') return 'Arguments are not sufficiently instantiated';
      if (f.t === 'c' && f.f === 'evaluation_error') return 'Arithmetic: evaluation error: ' + SWI(f.a[0], true);
      if (f.t === 'c' && f.f === 'existence_error') return SWI(f.a[0], false) + ' `' + SWI(f.a[1], true) + "' does not exist";
      if (f.t === 'c' && f.f === 'syntax_error') return 'Syntax error: ' + SWI(f.a[0], false);
      if (f.t === 'c' && f.f === 'domain_error') return 'Domain error: `' + SWI(f.a[0], false) + "' expected, found `" + SWI(f.a[1], true) + "'";
      return 'Unknown error term: ' + SWI(f, true);
    }
    if (t.t === 'c' && t.f === 'format' && t.a.length === 2) return P.format(t.a[0], t.a[1]);
    return 'Unknown message: ' + SWI(t, true);
  }
  P.messageText = messageText;
  det('message_to_codes/3', (a, e) => e.unify(a[2], P.codesList(messageText(a[0]))));
  // '$messages':translate_message//1 and print_message_lines/3, as print_message/2 uses them
  det('translate_message/3', (a, e) => e.unify(a[1], P.cons(Cmp('-', [Atom('~w'), list([Str(messageText(a[0]))])]), a[2])));
  det('print_message_lines/3', (a, e) => {
    const pre = textOf(a[1]); let line = '', outText = '';
    for (const x of listToArray(a[2]) || []) { const t = D(x); if (t.t === 'a' && t.n === 'nl') { outText += pre + line + '\n'; line = ''; } else if (t.t === 'c' && t.f === '-' && t.a.length === 2) line += P.format(t.a[0], t.a[1]); else if (t.t === 'c' && t.f === 'ansi' && t.a.length === 3) line += P.format(t.a[1], t.a[2]); else line += textOf(t); }
    if (line) outText += pre + line + '\n';
    put(e, a[0], outText); return true;
  });
  // library(csv): rows as row(F1, ...), numbers converted unless convert(false)
  function parseCSV(text, sep) {
    const rows = []; let row = [], f = '', q = false, quoted = false;
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
      if (q) { if (c === '"') { if (text[i + 1] === '"') { f += '"'; i++; } else q = false; } else f += c; continue; }
      if (c === '"' && f === '') { q = true; quoted = true; continue; }
      if (c === sep) { row.push({ f, quoted }); f = ''; quoted = false; continue; }
      if (c === '\n' || c === '\r') { if (c === '\r' && text[i + 1] === '\n') i++; row.push({ f, quoted }); rows.push(row); row = []; f = ''; quoted = false; continue; }
      f += c;
    }
    if (f !== '' || quoted || row.length) { row.push({ f, quoted }); rows.push(row); }
    return rows;
  }
  function csvRows(text, opts) {
    let functor = 'row', convert = true, sep = ',', strip = false;
    for (const o of listToArray(opts) || []) { const t = D(o); if (t.t !== 'c' || t.a.length !== 1) continue; const v = D(t.a[0]); if (t.f === 'functor') functor = textOf(v); if (t.f === 'convert') convert = v.n !== 'false'; if (t.f === 'separator') sep = String.fromCharCode(Number(v.v)); if (t.f === 'strip') strip = v.n === 'true'; }
    return parseCSV(text, sep).map((r) => Cmp(functor, r.map(({ f, quoted }) => { if (strip) f = f.trim(); if (convert && !quoted && /^[+-]?\d+(\.\d+)?([eE][+-]?\d+)?$/.test(f)) return /[.eE]/.test(f) ? Num(parseFloat(f), true) : Int(Number(f)); return Atom(f); })));
  }
  det('csv_read_file/2', (a, e) => e.unify(a[1], list(csvRows(fileText(e, resolvePath(e, textOf(a[0]))), NIL))));
  det('csv_read_file/3', (a, e) => e.unify(a[1], list(csvRows(fileText(e, resolvePath(e, textOf(a[0]))), a[2]))));
  det('csv_read_file_row/3', () => false); delete B['csv_read_file_row/3'];
  const csvField = (t) => { const s = textOf(t); return /[",\n\r]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s; };
  det('csv_write_file/2', (a, e) => { const x = io(e); const txt = (listToArray(a[1]) || []).map((r) => D(r).a.map(csvField).join(',') + '\r\n').join(''); x.writeFile(resolvePath(e, textOf(a[0])), txt, false); return true; });
  det('csv_write_file/3', (a, e) => B['csv_write_file/2'].fn([a[0], a[1]], e));

  // ---------------------------------------------------------------- the program and the system
  nondet('clause/2', function* (a, e) {
    let h = D(a[0]); if (h.t === 'c' && h.f === ':' && h.a.length === 2) h = D(h.a[1]);
    if (h.t === 'v') throw P.instErr();
    const cls = e.prog.preds.get(P.key(h)); if (!cls) return;
    for (const cl of cls.slice()) { const m = e.mark(); const mp = new Map(); if (e.unify(h, copy(cl.head, mp)) && e.unify(a[1], copy(cl.body, mp))) yield; e.undo(m); }
  });
  nondet('current_predicate/1', function* (a, e) {
    let s = D(a[0]);
    if (s.t === 'c' && s.f === ':' && s.a.length === 2) {
      const m = D(s.a[0]), fa = D(s.a[1]);
      // Module:Name/Arity: the module's own (renamed) predicate, or the plain one it exports
      if (m.t === 'a' && fa.t === 'c' && fa.f === '/' && D(fa.a[0]).t === 'a' && D(fa.a[1]).t === 'n') { const k1 = m.n + ':' + D(fa.a[0]).n + '/' + D(fa.a[1]).v, k2 = D(fa.a[0]).n + '/' + D(fa.a[1]).v; if ((e.prog.preds.get(k1) || []).length || (e.prog.preds.get(k2) || []).length || e.prog.dynamic.has(k1) || e.prog.dynamic.has(k2)) yield 'last'; return; }
      s = fa;
    }
    for (const k of e.prog.order) { if (!e.prog.preds.get(k).length && !e.prog.dynamic.has(k)) continue; const i = k.lastIndexOf('/'); const m = e.mark(); if (e.unify(s, Cmp('/', [Atom(k.slice(0, i)), Int(+k.slice(i + 1))]))) yield; e.undo(m); }
  });
  det('current_predicate/2', (a, e) => { const h = D(a[1]); if (h.t === 'v') return false; return e.prog.preds.has(P.key(h)) && e.unify(a[0], Atom(P.name(h))); });
  det('predicate_property/2', (a, e) => { let h = D(a[0]); if (h.t === 'c' && h.f === ':') h = D(h.a[1]); if (h.t === 'v') return false; const k = P.key(h); if (B[k] || P.CONTROL.has(k)) return e.unify(a[1], Atom('built_in')) || e.unify(a[1], Atom('defined')); if (!e.prog.preds.has(k)) return false; const p = D(a[1]); if (p.t === 'v') return e.unify(p, Atom('defined')); if (p.t === 'a' && p.n === 'dynamic') return e.prog.dynamic.has(k); if (p.t === 'c' && p.f === 'number_of_clauses') return e.unify(p.a[0], Int(e.prog.preds.get(k).length)); return p.t === 'a' && (p.n === 'defined' || p.n === 'visible'); });
  nondet('current_prolog_flag/2', function* (a, e) {
    const x = io(e) || {};
    const flags = [['argv', list((x.argv || []).map((s) => Atom(s)))], ['bounded', Atom('false')], ['dialect', Atom('swi')], ['version', Int(90000)], ['max_tagged_integer', Int(1152921504606846975)], ['min_tagged_integer', Int(-1152921504606846976)], ['double_quotes', Atom('codes')], ['os_argv', list(['swipl'].concat(x.argv || []).map((s) => Atom(s)))], ['executable', Atom('pl2detlog')], ['home', Atom('.')], ['unix', Atom('true')], ['encoding', Atom('utf8')]];
    for (const [k, v] of flags) { const m = e.mark(); if (e.unify(a[0], Atom(k)) && e.unify(a[1], v)) yield; e.undo(m); }
  });
  det('prolog_load_context/2', (a, e) => { const x = io(e) || {}; const k = textOf(a[0]); if (k === 'directory') return e.unify(a[1], Atom(x.loadDir || x.cwd || '.')); if (k === 'module') return e.unify(a[1], Atom('user')); return false; });
  // loading files while the program runs (as mnnaction loads mnns): the clauses are added to the
  // program and its directives run; library(...) modules are built in
  function loadAtRun(e, spec0) {
    let spec = D(spec0); if (spec.t === 'c' && spec.f === ':' && spec.a.length === 2) spec = D(spec.a[1]);
    if (spec.t === 'c' && spec.f === 'library') return true;
    for (const one of listToArray(spec) || [spec]) {
      let f = D(one); if (f.t === 'c' && f.f === ':' && f.a.length === 2) f = D(f.a[1]);
      if (f.t === 'c' && f.f === 'library') continue;
      const x = io(e) || {}, base = resolvePath(e, textOf(f));
      const path = [base, base + '.pl', base + '.pro'].find((c) => x.stat ? x.stat(c) === 'file' : x.readFile && x.readFile(c) != null);
      if (!path) throw existErr('source_sink', f);
      e.loaded = e.loaded || new Set(); if (e.loaded.has(path)) continue; e.loaded.add(path);
      const text = x.readFile(path), dir = path.replace(/\/[^/]*$/, '');
      const saveCwd = x.loadDir; x.loadDir = dir;
      try {
        let cls = P.readProgram(text); const fwds = [];
        // the module directive: the first directive that is one, before any clause (after :- encoding(..) say)
        let md = null; for (const c of cls) { const t0 = D(c.term); if (!(t0.t === 'c' && t0.f === ':-' && t0.a.length === 1)) break; const d0 = D(t0.a[0]); if (d0.t === 'c' && d0.f === 'module' && d0.a.length === 2) { md = d0; break; } }
        if (md && md.t === 'c' && md.f === 'module' && md.a.length === 2) {
          const r = P.renameModule(cls.map((c) => c.term), P.textOf(md.a[0]), P.moduleExports(md));
          P.notePrivates(e.prog, P.textOf(md.a[0]), r.privates);
          for (const fw of r.forwarders) if (!(e.prog.preds.get(fw.key) || []).length) { const added = e.prog.add(fw.clause); if (added) fwds.push(added); }
          (e.prog.moduleFiles = e.prog.moduleFiles || new Map()).set(P.textOf(md.a[0]), path);
          cls = cls.map((c, i) => ({ term: r.terms[i], vars: c.vars }));
        }
        e.loadedClauses = e.loadedClauses || new Map(); const mine = fwds; e.loadedClauses.set(path, mine);
        const inits = [];
        // term_expansion/2 and goal_expansion/2, as SWI-Prolog applies them while it loads (Starlog's)
        cls = expandClauses(e, cls);
        for (const c of cls) {
          const t = D(c.term);
          if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
            const d = D(t.a[0]), n = d.t === 'c' ? d.f : d.t === 'a' ? d.n : '';
            if (['module', 'use_module', 'ensure_loaded', 'consult', 'include', 'load_files', 'reexport'].includes(n)) {
              if (n !== 'module') { const sv = x.cwd; x.cwd = dir; try { loadAtRun(e, d.a[0]); } finally { x.cwd = sv; } }
              continue;
            }
            if (n === 'dynamic' || n === 'discontiguous') { for (const s2 of P.commaList(d.a[0])) { const sd = D(s2); if (sd.t === 'c' && sd.f === '/') { const k = P.name(sd.a[0]) + '/' + D(sd.a[1]).v; if (n === 'dynamic') e.prog.dynamic.add(k); if (!e.prog.preds.has(k)) { e.prog.preds.set(k, []); e.prog.order.push(k); } } } continue; }
            if (n === 'initialization') { inits.push(d.a[0]); continue; } // run when the file is loaded
            if (['set_prolog_flag', 'license', 'meta_predicate', 'multifile', 'table', 'module_transparent', 'public', 'encoding', 'style_check'].includes(n)) continue;
            e.solve(d, () => false);
            continue;
          }
          const added = e.prog.add(t, c.vars); if (added) mine.push(added);
        }
        for (const g of inits) { const m = e.mark(); e.solve(g, () => false); e.undo(m); }
      } finally { x.loadDir = saveCwd; }
    }
    return true;
  }
  const hasClauses = (e, k) => (e.prog.preds.get(k) || []).length > 0;
  function callOnce(e, goal, out) {
    const m = e.mark(); let r = null;
    try { e.solve(goal, () => { r = P.copy(P.resolve(out)); return false; }); } catch (x) { if (x && x.halt) throw x; r = null; }
    e.undo(m); return r;
  }
  function expandGoals(e, g, depth = 0) {
    g = D(g);
    if (g.t === 'v' || depth > 40) return g;
    const k = P.key(g); if (!k) return g;
    if (GOAL_POS[k]) { const a = g.a.slice(); for (const i of GOAL_POS[k]) a[i] = expandGoals(e, a[i], depth); return { t: 'c', f: g.f, a }; }
    const X = Var(), r = callOnce(e, Cmp('goal_expansion', [g, X]), Cmp('x', [g, X]));
    if (r && !P.variant(D(r.a[1]), g)) { return expandGoals(e, D(r.a[1]), depth + 1); }
    return g;
  }
  P.variant = (a, b) => P.variantKey(a) === P.variantKey(b);
  function expandClauses(e, cls) {
    const te = hasClauses(e, 'term_expansion/2'), ge = hasClauses(e, 'goal_expansion/2');
    if (!te && !ge) return cls;
    const out = [];
    for (const c of cls) {
      let ts = [c.term];
      const t0 = D(c.term);
      const directive = t0.t === 'c' && t0.f === ':-' && t0.a.length === 1;
      if (te && !directive) {
        const X = Var(); const r = callOnce(e, Cmp('term_expansion', [c.term, X]), Cmp('x', [c.term, X]));
        if (r) { const x = D(r.a[1]); ts = listToArray(x) || [x]; }
      }
      for (let t of ts) {
        t = D(t);
        if (ge) {
          if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = Cmp(':-', [t.a[0], expandGoals(e, t.a[1])]);
          else if (t.t === 'c' && t.f === ':-' && t.a.length === 1) t = Cmp(':-', [expandGoals(e, t.a[0])]);
        }
        out.push({ term: t, vars: c.vars });
      }
    }
    return out;
  }
  P.expandClauses = expandClauses;
  det('expand_goal/2', (a, e) => e.unify(a[1], hasClauses(e, 'goal_expansion/2') ? expandGoals(e, a[0]) : a[0]));
  det('expand_term/2', (a, e) => { if (!hasClauses(e, 'term_expansion/2')) return e.unify(a[1], a[0]); const X = Var(); const r = callOnce(e, Cmp('term_expansion', [a[0], X]), Cmp('x', [a[0], X])); return e.unify(a[1], r ? r.a[1] : a[0]); });
  det('consult/1', (a, e) => loadAtRun(e, a[0]));
  det('ensure_loaded/1', (a, e) => loadAtRun(e, a[0]));
  det('use_module/1', (a, e) => loadAtRun(e, a[0]));
  det('use_module/2', (a, e) => loadAtRun(e, a[0]));
  det('load_files/2', (a, e) => loadAtRun(e, a[0]));
  det('module/2', () => true);
  det('=@=/2', (a) => P.variantKey(a[0]) === P.variantKey(a[1]));
  det('\\=@=/2', (a) => P.variantKey(a[0]) !== P.variantKey(a[1]));
  det('op/3', (a) => { P.applyOpDirective(Cmp('op', a)); return true; });
  det('set_prolog_flag/2', () => true);
  det('license/1', () => true);
  det('initialization/1', () => true);
  det('initialization/2', () => true);
  det('table/1', () => true);
  det('meta_predicate/1', () => true);
  det('multifile/1', () => true);
  det('module_transparent/1', () => true);
  det('public/1', () => true);
  det('nb_current/2', (a, e) => { const k = D(a[0]); if (k.t === 'v') return false; const v = e.globals.get(textOf(k)); return !!v && e.unify(a[1], v); });
  det('tmp_file/2', (a, e) => e.unify(a[1], Atom('/tmp/pl_' + textOf(a[0]) + '_' + (++e.streamSeq))));
  det('ground/1', (a) => isGround(a[0]));
  det('string_code/3', (a, e) => { const i = Number(P.evalArith(a[0]).v), s = textOf(a[1]); return i >= 1 && i <= s.length && e.unify(a[2], Int(s.charCodeAt(i - 1))); });
  det('sumlist/2', B['sum_list/2'].fn);
  det('term_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Atom(SWI(t, true))); const r = P.readTerm(textOf(a[1])); return e.unify(t, r.term); });
  det('with_output_to_string/2', () => false); delete B['with_output_to_string/2'];
  det('ansi_format/3', (a, e) => { e.write(P.format(a[1], a[2])); return true; });
  det('sleep/1', () => true);
  det('shell/0', () => true);
  det('garbage_collect_atoms/0', () => true);
  det('statistics/0', () => true);
  det('assertion/1', () => true); // replaced by the prelude's definition
  delete B['assertion/1'];
  callb(':/2', (a, e) => {
    const m = D(a[0]), g = D(a[1]);
    if (m.t === 'a' && (g.t === 'a' || g.t === 'c')) { const f = g.t === 'a' ? g.n : g.f, n = g.t === 'a' ? 0 : g.a.length; const pk = m.n + ':' + f + '/' + n; if (e.prog.preds.has(pk)) return g.t === 'a' ? Atom(m.n + ':' + f) : { t: 'c', f: m.n + ':' + f, a: g.a };
      // a library module (lists, apply, ..: not one the program loaded): its built-in, not a user predicate of that name
      if (g.t === 'c' && B[f + '/' + n] && m.n !== 'user' && !(e.prog.moduleFiles && e.prog.moduleFiles.has(m.n))) return { t: 'c', f: g.f, a: g.a, lib: true }; }
    return g;
  });
  callb('setup_call_cleanup/3', (a) => Cmp('$scc', [a[0], a[1], a[2]]));
  callb('call_cleanup/2', (a) => Cmp('$scc', [Atom('true'), a[0], a[1]]));

  // ---- modules: a module's private predicates are renamed 'Module:name', so that two modules can
  // each have their own helper of the same name; exported predicates keep their names. Calls in the
  // module (and in its meta-arguments: maplist(helper, ...), findall(_, helper(..), _), lambdas)
  // are renamed with them; Module:Goal calls Module's own; a goal built at run time that names a
  // private predicate finds it through prog.privates.
  const CLOSURE_EXTRA = { 'maplist/2': 1, 'maplist/3': 2, 'maplist/4': 3, 'maplist/5': 4, 'maplist/6': 5, 'maplist/7': 6, 'foldl/4': 3, 'foldl/5': 4, 'foldl/6': 5, 'foldl/7': 6, 'include/3': 1, 'exclude/3': 1, 'partition/4': 1, 'partition/6': 2, 'convlist/3': 2, 'max_member/3': 2, 'min_member/3': 2, 'predsort/3': 3, 'map_list_to_pairs/3': 2, 'call/2': 1, 'call/3': 2, 'call/4': 3, 'call/5': 4, 'call/6': 5, 'call/7': 6, 'call/8': 7, 'aggregate_all/3': -1 };
  const GOAL_POS = { ',/2': [0, 1], ';/2': [0, 1], '->/2': [0, 1], '*->/2': [0, 1], '\\+/1': [0], 'not/1': [0], 'call/1': [0], 'once/1': [0], 'ignore/1': [0], 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'bagof/3': [1], 'setof/3': [1], 'aggregate_all/3': [1], 'aggregate_all/4': [2], 'catch/3': [0, 2], '^/2': [1], 'with_output_to/2': [1], 'setup_call_cleanup/3': [0, 1, 2], 'call_cleanup/2': [0, 1], 'time/1': [0], 'call_with_time_limit/2': [1], 'call_with_inference_limit/3': [0], 'with_mutex/2': [1], 'tabled_call/1': [0], 'phrase/2': [], 'phrase/3': [], 'initialization/1': [0], 'initialization/2': [0] };
  const DBK = new Set(['assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'retractall/1', 'clause/2', 'abolish/1']);
  function renameModule(terms, M, exportKeys) {
    const local = new Set();
    const headKey = (t) => { t = D(t); if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = D(t.a[0]); while (t.t === 'c' && t.f === ':' && t.a.length === 2) t = D(t.a[1]); if (t.t === 'c' && t.f === '-->' && t.a.length === 2) { let h = D(t.a[0]); if (h.t === 'c' && h.f === ',') h = D(h.a[0]); const k = P.key(h); if (!k) return null; const i = k.lastIndexOf('/'); return k.slice(0, i) + '/' + (+k.slice(i + 1) + 2); } return P.key(t); };
    // a clause whose head names another module (user:term_expansion(..)) belongs to that module: it keeps its name
    const foreign = (t) => { t = D(t); if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = D(t.a[0]); return t.t === 'c' && t.f === ':' && t.a.length === 2 && D(t.a[0]).t === 'a' && D(t.a[0]).n !== M; };
    for (const t of terms) { if (foreign(t)) continue; const d = D(t); if (d.t === 'c' && d.f === ':-' && d.a.length === 1) { const g = D(d.a[0]); if (g.t === 'c' && (g.f === 'dynamic' || g.f === 'discontiguous' || g.f === 'table')) for (const x of P.commaList(g.a[0])) { const sd = D(x); if (sd.t === 'c' && sd.f === '/' && D(sd.a[0]).t !== 'c') local.add(P.name(sd.a[0]) + '/' + D(sd.a[1]).v); } continue; } const k = headKey(t); if (k) local.add(k); }
    // every predicate of the module is renamed (so the module always calls its own); an exported one
    // also gets a plain-named forwarder (the first module to export a name keeps it). Dynamic ones that
    // are exported keep their plain name, as other modules may assert them.
    const dyn = new Set();
    for (const t of terms) { const d = D(t); if (d.t === 'c' && d.f === ':-' && d.a.length === 1) { const g = D(d.a[0]); if (g.t === 'c' && g.f === 'dynamic') for (const x of P.commaList(g.a[0])) { const sd = D(x); if (sd.t === 'c' && sd.f === '/') dyn.add(P.name(sd.a[0]) + '/' + D(sd.a[1]).v); } } }
    const priv = new Set([...local].filter((k) => !(exportKeys.has(k) && dyn.has(k))));
    if (!priv.size) return { terms, privates: [], forwarders: [] };
    const rn = (name) => M + ':' + name;
    const renameHead = (h) => { h = D(h); if (h.t === 'c' && h.f === ':' && h.a.length === 2 && D(h.a[0]).t === 'a' && D(h.a[0]).n !== M) return D(h.a[1]); while (h.t === 'c' && h.f === ':' && h.a.length === 2) h = D(h.a[1]); const k = P.key(h); if (!priv.has(k)) return h; return h.t === 'a' ? Atom(rn(h.n)) : { t: 'c', f: rn(h.f), a: h.a }; };
    const closure = (c, extra) => {
      c = D(c);
      if (c.t === 'c' && c.f === '>>' && c.a.length === 2) return { t: 'c', f: '>>', a: [c.a[0], goal(c.a[1])] };
      if (c.t === 'c' && c.f === ':' && c.a.length === 2) return qualified(c);
      const k = c.t === 'a' ? c.n + '/' + extra : c.t === 'c' ? c.f + '/' + (c.a.length + extra) : null;
      if (!k || !priv.has(k)) return c;
      return c.t === 'a' ? Atom(rn(c.n)) : { t: 'c', f: rn(c.f), a: c.a };
    };
    const qualified = (g) => { const m = D(g.a[0]); if (m.t === 'a' && m.n === M) return goal(g.a[1]); return g; };
    function goal(g) {
      g = D(g);
      if (g.t === 'v') return g;
      if (g.t === 'c' && g.f === ':' && g.a.length === 2) return qualified(g);
      const k = P.key(g); if (!k) return g;
      if (GOAL_POS[k]) { const a = g.a.slice(); for (const i of GOAL_POS[k]) a[i] = goal(a[i]); if (k === 'phrase/2' || k === 'phrase/3') a[0] = closure(a[0], 2); return { t: 'c', f: g.f, a }; }
      if (CLOSURE_EXTRA[k] > 0) { const a = g.a.slice(); a[0] = closure(a[0], CLOSURE_EXTRA[k]); return { t: 'c', f: g.f, a }; }
      if (g.t === 'c' && g.f === '>>') return { t: 'c', f: '>>', a: [g.a[0], goal(g.a[1])].concat(g.a.slice(2)) };
      if (DBK.has(k) && g.a.length) { const a = g.a.slice(); a[0] = dbArg(a[0]); return { t: 'c', f: g.f, a }; }
      if (priv.has(k)) return g.t === 'a' ? Atom(rn(g.n)) : { t: 'c', f: rn(g.f), a: g.a };
      return g;
    }
    // assert(foo(..)), retract((foo(..) :- B)): the clause's head names a predicate of the module
    function dbArg(c) { c = D(c); if (c.t === 'c' && c.f === ':-' && c.a.length === 2) return Cmp(':-', [renameHead(c.a[0]), goal(c.a[1])]); if (c.t === 'c' && c.f === ':' && c.a.length === 2) return c; return c.t === 'v' ? c : renameHead(c); }
    const out = terms.map((t) => {
      const d = D(t);
      if (d.t === 'c' && d.f === ':-' && d.a.length === 2) return Cmp(':-', [renameHead(d.a[0]), goal(d.a[1])]);
      if (d.t === 'c' && d.f === ':-' && d.a.length === 1) {
        const g = D(d.a[0]);
        if (g.t === 'c' && (g.f === 'dynamic' || g.f === 'discontiguous' || g.f === 'table')) return Cmp(':-', [Cmp(g.f, [P.conj(P.commaList(g.a[0]).map((x) => { const sd = D(x); return sd.t === 'c' && sd.f === '/' && priv.has(P.name(sd.a[0]) + '/' + D(sd.a[1]).v) ? Cmp('/', [Atom(rn(P.name(sd.a[0]))), sd.a[1]]) : sd; }))])]);
        return Cmp(':-', [goal(g)]);
      }
      if (d.t === 'c' && d.f === '-->' && d.a.length === 2) { const tr = P.dcgTransform(d); return Cmp(':-', [renameHead(tr.a[0]), goal(tr.a[1])]); }
      return renameHead(d);
    });
    const forwarders = [...priv].filter((k) => exportKeys.has(k)).map((k) => { const i = k.lastIndexOf('/'), f = k.slice(0, i), n = +k.slice(i + 1); const vs = Array.from({ length: n }, () => Var()); return { key: k, clause: n ? Cmp(':-', [Cmp(f, vs), Cmp(rn(f), vs)]) : Cmp(':-', [Atom(f), Atom(rn(f))]) }; });
    return { terms: out, privates: [...priv].filter((k) => !exportKeys.has(k)), forwarders };
  }
  P.renameModule = renameModule;
  P.moduleExports = (d) => { const ex = new Set(); for (const x of listToArray(D(d).a[1]) || []) { const t = D(x); if (t.t === 'c' && (t.f === '/' || t.f === '//') && t.a.length === 2) ex.add(P.name(t.a[0]) + '/' + (Number(D(t.a[1]).v) + (t.f === '//' ? 2 : 0))); } return ex; };
  P.notePrivates = (prog, M, privs) => { prog.privates = prog.privates || new Map(); for (const k of privs) { const i = k.lastIndexOf('/'); const plain = k.slice(0, i) + '/' + k.slice(i + 1); if (!prog.privates.has(plain)) prog.privates.set(plain, []); prog.privates.get(plain).push(M + ':' + k.slice(0, i)); } };

  // ---- functional notation on dicts: a goal with Dict.Func in it first evaluates ./3
  const hasDots = (t) => { t = D(t); return t.t === 'c' && (t.f === '$dot' && t.a.length === 2 || t.a.some(hasDots)); };
  P.hasDots = hasDots;
  const GOALARGS = { ',/2': [0, 1], ';/2': [0, 1], '->/2': [0, 1], '*->/2': [0, 1], '\\+/1': [0], 'call/1': [0], 'once/1': [0], 'ignore/1': [0], 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'bagof/3': [1], 'setof/3': [1], 'aggregate_all/3': [1], 'catch/3': [0, 2], '^/2': [1] };
  function pullDots(t, pre) {
    t = D(t);
    if (t.t !== 'c') return t;
    const args = t.a.map((x) => pullDots(x, pre));
    if (t.f === '$dot' && t.a.length === 2) { const V = Var(); pre.push(Cmp('.', [args[0], args[1], V])); return V; }
    return { t: 'c', f: t.f, a: args };
  }
  function expandGoal(g) {
    g = D(g);
    if (g.t !== 'c') return g;
    const k = g.f + '/' + g.a.length;
    if (GOALARGS[k]) { const a = g.a.slice(); for (const i of GOALARGS[k]) a[i] = expandGoal(a[i]); for (let i = 0; i < a.length; i++) if (!GOALARGS[k].includes(i) && hasDots(a[i])) { const pre = []; a[i] = pullDots(a[i], pre); if (pre.length) return P.conj(pre.concat([{ t: 'c', f: g.f, a }])); } return { t: 'c', f: g.f, a }; }
    if (!hasDots(g)) return g;
    const pre = []; const ng = pullDots(g, pre);
    return P.conj(pre.concat([ng]));
  }
  P.expandDots = (cl) => {
    cl = D(cl);
    let h = cl, b = Atom('true');
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 2) { h = D(cl.a[0]); b = cl.a[1]; }
    else if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 1) return Cmp(':-', [expandGoal(cl.a[0])]);
    const pre = []; h = pullDots(h, pre);
    const body = expandGoal(b);
    return Cmp(':-', [h, pre.length ? P.conj(pre.concat([body])) : body]);
  };
  det('./3', (a, e) => {
    const d = D(a[0]), f = D(a[1]);
    if (f.t === 'a' || f.t === 'n') { const ps = dictOf(d); const p = ps.find(([k]) => compare(k, f) === 0); if (!p) throw err(Cmp('existence_error', [Atom('key'), f, d])); return e.unify(a[2], p[1]); }
    if (f.t === 'c' && f.f === 'get' && f.a.length === 1) { const ps = dictOf(d); const p = ps.find(([k]) => compare(k, D(f.a[0])) === 0); return !!p && e.unify(a[2], p[1]); }
    if (f.t === 'c' && f.f === 'get' && f.a.length === 2) { const ps = dictOf(d); const p = ps.find(([k]) => compare(k, D(f.a[0])) === 0); return e.unify(a[2], p ? p[1] : f.a[1]); }
    if (f.t === 'c' && f.f === 'put' && f.a.length === 1) return B['put_dict/3'].fn([f.a[0], d, a[2]], e);
    if (f.t === 'c' && f.f === 'put' && f.a.length === 2) return B['put_dict/4'].fn([f.a[0], d, f.a[1], a[2]], e);
    throw err(Cmp('existence_error', [Atom('dict_function'), f]));
  });

  // ---- more of SWI-Prolog's library (as mnns uses it)
  nondet('stream_property/2', function* (a, e) {
    const s = streamOf(e, a[0]);
    const props = [Cmp('mode', [Atom(s.mode || 'read')])];
    if (s.path) props.push(Cmp('file_name', [Atom(s.path)]));
    if (s.alias) props.push(Cmp('alias', [Atom(s.alias)]));
    if (s.text !== undefined) props.push(Cmp('position', [Cmp('$stream_position', [Int(s.pos), Int(s.line || 1), Int(0), Int(s.pos)])]));
    if (s.mode === 'read') props.push(Atom('input')); else props.push(Atom('output'));
    props.push(Cmp('encoding', [Atom('utf8')]));
    for (const p of props) { const m = e.mark(); if (e.unify(a[1], p)) yield; e.undo(m); }
  });
  det('stream_position_data/3', (a, e) => { const f = textOf(a[0]), p = D(a[1]); if (p.t !== 'c') return false; const i = { char_count: 0, line_count: 1, line_position: 2, byte_count: 3 }[f]; return i !== undefined && e.unify(a[2], p.a[i]); });
  det('set_stream_position/2', (a, e) => { const s = streamOf(e, a[0]); const p = D(a[1]); s.pos = Number(D(p.a[0]).v); s.line = Number(D(p.a[1]).v); return true; });
  det('line_count/2', (a, e) => e.unify(a[1], Int(streamOf(e, a[0]).line || 1)));
  det('open_string/2', (a, e) => { const id = ++e.streamSeq; e.streams.set(id, { id, mode: 'read', text: textOf(a[0]), pos: 0, line: 1 }); return e.unify(a[1], Cmp('$stream', [Int(id)])); });
  det('tmp_file_stream/3', (a, e) => {
    const x = io(e); if (!x || !x.writeFile) throw permErr('open', 'source_sink', Atom('tmp'));
    const path = (x.tmpDir || '/tmp').replace(/\/$/, '') + '/pl2d_' + Date.now().toString(36) + '_' + (++e.streamSeq) + '.pl';
    x.writeFile(path, '', false);
    const id = ++e.streamSeq; e.streams.set(id, { id, mode: 'write', path, buf: '' });
    return e.unify(a[1], Atom(path)) && e.unify(a[2], Cmp('$stream', [Int(id)]));
  });
  det('rename_file/2', (a, e) => { const x = io(e); if (!x || !x.rename) throw permErr('rename', 'file', a[0]); const p = resolvePath(e, textOf(a[0])); ioDo('rename', p, () => x.rename(p, resolvePath(e, textOf(a[1])))); return true; });
  det('unload_file/1', (a, e) => {
    const path = resolvePath(e, textOf(a[0])); const cls = e.loadedClauses && e.loadedClauses.get(path); if (!cls) return true;
    for (const cl of cls) { const k = P.key(cl.head); const l = e.prog.preds.get(k); if (l) { const i = l.indexOf(cl); if (i >= 0) l.splice(i, 1); if (!l.length && !e.prog.dynamic.has(k)) { e.prog.preds.delete(k); const j = e.prog.order.indexOf(k); if (j >= 0) e.prog.order.splice(j, 1); } } }
    e.loadedClauses.delete(path); if (e.loaded) e.loaded.delete(path); return true;
  });
  nondet('sub_term/2', function* (a, e) {
    const all = []; (function walk(t) { t = D(t); all.push(t); if (t.t === 'c') t.a.forEach(walk); })(a[1]);
    for (const t of all) { const m = e.mark(); if (e.unify(a[0], t)) yield; e.undo(m); }
  });
  det('compound_name_arguments/3', (a, e) => { const t = D(a[0]); if (t.t === 'c') return e.unify(a[1], Atom(t.f)) && e.unify(a[2], list(t.a)); const args = listToArray(a[2]) || []; return e.unify(t, { t: 'c', f: textOf(a[1]), a: args }); });
  det('compound_name_arity/3', (a, e) => { const t = D(a[0]); if (t.t === 'c') return e.unify(a[1], Atom(t.f)) && e.unify(a[2], Int(t.a.length)); const n = Number(D(a[2]).v); return e.unify(t, { t: 'c', f: textOf(a[1]), a: Array.from({ length: n }, () => Var()) }); });
  det('acyclic_term/1', () => true);
  det('cyclic_term/1', () => false);
  nondet('current_module/1', function* (a, e) { for (const m of ['user', 'system']) { const k = e.mark(); if (e.unify(a[0], Atom(m))) yield; e.undo(k); } });
  nondet('module_property/2', function* (a, e) {
    const files = e.prog.moduleFiles || new Map(); const m = D(a[0]);
    for (const [mod, f] of files) { if (m.t !== 'v' && m.n !== mod) continue; const k = e.mark(); if (e.unify(a[0], Atom(mod)) && e.unify(a[1], Cmp('file', [Atom(f)]))) yield; e.undo(k); }
  });
  det('set_random/1', () => true);
  det('directory_file_path/3', (a, e) => { const d = D(a[0]), f = D(a[1]); if (d.t !== 'v' && f.t !== 'v') return e.unify(a[2], Atom(P.joinPath(textOf(d), textOf(f)))); const p = textOf(a[2]); const i = p.lastIndexOf('/'); return e.unify(d, Atom(i < 0 ? '.' : p.slice(0, i))) && e.unify(f, Atom(p.slice(i + 1))); });
  det('numbervars/4', (a, e) => {
    const single = (listToArray(a[3]) || []).some((x) => { x = D(x); return x.t === 'c' && x.f === 'singletons' && D(x.a[0]).n === 'true'; });
    let n = Number(D(a[1]).v);
    const counts = new Map(); (function walk(x) { x = D(x); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') x.a.forEach(walk); })(a[0]);
    for (const v of P.termVars(a[0])) e.bind(v, Cmp('$VAR', [single && counts.get(v) === 1 ? Atom('_') : Int(n++)]));
    return e.unify(a[2], Int(n));
  });
  // as SWI-Prolog's portray_clause/1 lays a clause out: variables A, B, ... (one seen once is _),
  // one goal a line, disjunctions and if-then-else in columns, meta-arguments that are control
  // constructs one argument a line
  const PC_META = { 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'aggregate_all/3': [1], 'aggregate_all/4': [2], 'bagof/3': [1], 'setof/3': [1], 'once/1': [0], 'ignore/1': [0], '\\+/1': [0], 'call/1': [0], 'catch/3': [0, 2], 'with_output_to/2': [1], 'time/1': [0], 'setup_call_cleanup/3': [0, 1, 2], 'call_cleanup/2': [0, 1] };
  const isControl = (g) => { g = D(g); return g.t === 'c' && g.a.length === 2 && (g.f === ',' || g.f === ';' || g.f === '->' || g.f === '*->'); };
  function portray(t) {
    const c = P.copy(t);
    const counts = new Map(); (function walk(x) { x = D(x); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') x.a.forEach(walk); })(c);
    const names = new Map(); let n = 0;
    const o = { quoted: true, swi: true, nextArg: true, varName: (v) => { if (counts.get(v) === 1) return '_'; if (!names.has(v)) names.set(v, P.letters(n++)); return names.get(v); } };
    const pad = (k) => ' '.repeat(k);
    const term = (x, prec) => show(x, Object.assign({ prec }, o));
    // a goal at column col (the text starts there; later lines are indented from col)
    function goal(g, col) {
      g = D(g);
      if (g.t === 'c' && g.a.length === 2 && (g.f === ';' || g.f === '->' || g.f === '*->')) return disj(g, col);
      const k = P.key(g);
      if (k === '\\+/1' && isControl(g.a[0])) return '\\+' + block(g.a[0], col + 2);
      if (PC_META[k] && PC_META[k].some((i) => isControl(g.a[i]))) {
        const nm = P.fmtAtom(g.f, true) + '(', c2 = col + nm.length;
        if (g.a.length === 1) return nm + block(g.a[0], c2) + ')';
        return nm + g.a.map((x, i) => (i ? pad(c2) : '') + (PC_META[k].includes(i) && isControl(x) ? block(x, c2) : term(x, 999))).join(',\n') + ')';
      }
      return term(g, 999);
    }
    function conjAt(g, col) { const gs = P.commaList(g).length ? flat(g) : [g]; return gs.map((x, i) => (i ? pad(col) : '') + goal(x, col)).join(',\n'); }
    function flat(g) { g = D(g); return g.t === 'c' && g.f === ',' && g.a.length === 2 ? flat(g.a[0]).concat(flat(g.a[1])) : [g]; }
    function block(g, col) {
      g = D(g);
      if (g.t === 'c' && g.f === ',' && g.a.length === 2) return '( ' + conjAt(g, col + 2) + '\n' + pad(col) + ')';
      if (g.t === 'c' && g.a.length === 2 && (g.f === ';' || g.f === '->' || g.f === '*->')) return disj(g, col);
      return goal(g, col);
    }
    function disj(g, col) {
      const parts = [];
      (function alt(x, first) {
        x = D(x);
        if (x.t === 'c' && x.f === ';' && x.a.length === 2) { alt(x.a[0], first); alt(x.a[1], false); return; }
        const lead = first ? '(   ' : ';   ';
        if (x.t === 'c' && (x.f === '->' || x.f === '*->') && x.a.length === 2) { parts.push(lead + conjAt(x.a[0], col + 4)); parts.push((x.f === '->' ? '->  ' : '*-> ') + conjAt(x.a[1], col + 4)); return; }
        parts.push(lead + conjAt(x, col + 4));
      })(g, true);
      return parts.map((p, i) => (i ? pad(col) : '') + p).join('\n') + '\n' + pad(col) + ')';
    }
    const d = D(c);
    if (d.t === 'c' && d.f === ':-' && d.a.length === 2) {
      const b = D(d.a[1]);
      if (b.t === 'a' && b.n === 'true') return term(d.a[0], 1199) + '.\n';
      return term(d.a[0], 1199) + ' :-\n' + pad(4) + conjAt(b, 4) + '.\n';
    }
    if (d.t === 'c' && d.f === ':-' && d.a.length === 1) return ':- ' + conjAt(d.a[0], 3) + '.\n';
    return term(d, 1199) + '.\n';
  }
  P.portrayClause = portray;
  det('portray_clause/1', (a, e) => { e.write(portray(a[0])); return true; });
  det('portray_clause/2', (a, e) => { put(e, a[0], portray(a[1])); return true; });
  det('call_with_depth_limit/3', () => false); delete B['call_with_depth_limit/3'];
  callb('with_mutex/2', (a) => Cmp('once', [a[1]]));
  // term_string/3 and term_to_atom with read options (variable_names(Vs), variables(Vs))
  const readOpts = (e, opts, r) => bindReadOpts(e, opts, r);
  det('term_string/3', (a, e) => { const t = D(a[0]); const s0 = D(a[1]); if (s0.t === 'v') return e.unify(s0, Str(SWI(t, true))); const r = P.readTerm(textOf(s0)); if (P.hasDots(r.term)) r.term = P.expandDots(Cmp(':-', [Atom('$t'), r.term])).a[1]; readOpts(e, a[2], r); return e.unify(t, r.term); });
  det('term_string/2', (a, e) => { const t = D(a[0]); const s0 = D(a[1]); if (s0.t === 'v') return e.unify(s0, Str(SWI(t, true))); return e.unify(t, P.readTerm(textOf(s0)).term); });
  det('read_term_from_atom/3', (a, e) => { const r = P.readTerm(textOf(a[0])); readOpts(e, a[2], r); return e.unify(a[1], r.term); });
  det('term_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v' && D(a[1]).t === 'v') return e.unify(a[1], Atom(SWI(t, true))); return e.unify(t, P.readTerm(textOf(a[1])).term); });
  det('flag/3', (a, e) => { e.flags3 = e.flags3 || new Map(); const k = show(a[0], { quoted: true }); const old = e.flags3.get(k) || Int(0); if (!e.unify(a[1], old)) return false; const n = D(a[2]); e.flags3.set(k, n.t === 'n' ? n : P.evalArith(n)); return true; });
  // ---- clauses asserted into a module (assertz(M:Clause)): the head becomes 'M:name' and each call
  // in the body M:Goal, which finds M's own predicate first (as a module's clauses would)
  const SYSMOD = new Set(['user', 'system', 'lists', 'apply']);
  function intoModule(M, cl) {
    cl = D(cl);
    let h = cl, b = null;
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 2) { h = D(cl.a[0]); b = cl.a[1]; }
    const hh = h.t === 'a' ? Atom(M + ':' + h.n) : { t: 'c', f: M + ':' + h.f, a: h.a };
    if (!b) return hh;
    const wrap = (g) => {
      g = D(g); if (g.t === 'v') return Cmp(':', [Atom(M), g]);
      const k = P.key(g); if (!k) return g;
      if (GOAL_POS[k]) { const a = g.a.slice(); for (const i of GOAL_POS[k]) a[i] = wrap(a[i]); return { t: 'c', f: g.f, a }; }
      if (k === ':/2' || B[k] || P.CONTROL.has(k)) return g;
      return Cmp(':', [Atom(M), g]);
    };
    return Cmp(':-', [hh, wrap(b)]);
  }
  const modClause = (t) => { t = D(t); if (t.t === 'c' && t.f === ':' && t.a.length === 2) { const m = D(t.a[0]); if (m.t === 'a' && !SYSMOD.has(m.n)) return intoModule(m.n, t.a[1]); return D(t.a[1]); } return t; };
  det('assert/1', (a, e) => { e.prog.add(copy(modClause(a[0]))); return true; });
  det('assertz/1', (a, e) => { e.prog.add(copy(modClause(a[0]))); return true; });
  det('asserta/1', (a, e) => { e.prog.add(copy(modClause(a[0])), null, false); return true; });
  det('$drop_module/1', (a, e) => { const pre = textOf(a[0]) + ':'; for (const k of e.prog.order) if (k.startsWith(pre)) e.prog.preds.set(k, []); return true; });
  callb('in_temporary_module/3', (a, e) => { const M = Atom('$tmp_module_' + (++e.streamSeq)); return Cmp(',', [Cmp('=', [a[0], M]), Cmp('$scc', [Atom('true'), Cmp(',', [a[1], a[2]]), Cmp('$drop_module', [M])])]); });
  det('gensym/2', (a, e) => { e.gensyms = e.gensyms || new Map(); const b = textOf(a[0]); const n = (e.gensyms.get(b) || 0) + 1; e.gensyms.set(b, n); return e.unify(a[1], Atom(b + n)); });
  det('reset_gensym/1', (a, e) => { if (e.gensyms) e.gensyms.delete(textOf(a[0])); return true; });
  det('reset_gensym/0', (a, e) => { e.gensyms = new Map(); return true; });
  // limits: a nested run with its own step budget or deadline
  function limited(e, goal, budget, onLimit) {
    const was = e.stepLimit, m = e.mark(); let ok = false;
    e.stepLimit = budget;
    try { e.solve(goal, () => { ok = true; return false; }); }
    catch (x) { e.stepLimit = was; if (x instanceof P.LimitError && x.inner) { e.undo(m); return onLimit(); } throw x; }
    e.stepLimit = was;
    if (!ok) e.undo(m);
    return ok;
  }
  // LimitError from a nested budget is marked inner, so an outer limit is not mistaken for it
  function budgetSteps(e, n) { const lim = e.steps + n, outer = e.stepLimit; return { valueOf() { if (e.steps > lim) { const x = new P.LimitError('inference limit'); x.inner = true; throw x; } return Number(outer); }, toString() { return String(outer); } }; }
  function budgetTime(e, ms) { const dl = P.now() + ms, outer = e.stepLimit; let n = 0; return { valueOf() { if ((++n & 1023) === 0 && P.now() > dl) { const x = new P.LimitError('time limit'); x.inner = true; throw x; } return Number(outer); }, toString() { return String(outer); } }; }
  det('call_with_inference_limit/3', (a, e) => {
    const n = Number(P.evalArith(a[1]).v);
    let res = Atom('!');
    const ok = limited(e, a[0], budgetSteps(e, n), () => { res = Atom('inference_limit_exceeded'); return true; });
    return ok && e.unify(a[2], res);
  });
  det('call_with_time_limit/2', (a, e) => limited(e, a[1], budgetTime(e, Number(P.evalArith(a[0]).v) * 1000), () => { throw new P.PlError(Atom('time_limit_exceeded')); }));
  det('call_with_time_limit/3', (a, e) => limited(e, a[1], budgetTime(e, Number(P.evalArith(a[0]).v) * 1000), () => { throw new P.PlError(Atom('time_limit_exceeded')); }));
  nondet('limit/2', function* (a, e) {
    const n = Number(P.evalArith(a[0]).v), sols = [];
    const tmpl = Cmp('v', P.termVars(a[1]));
    if (n > 0) { const m = e.mark(); e.solve(a[1], () => { sols.push(P.copy(P.resolve(tmpl))); return sols.length < n; }); e.undo(m); }
    for (const s1 of sols) { const m = e.mark(); if (e.unify(tmpl, s1)) yield; e.undo(m); }
  });
  det('subset/2', (a, e) => { const xs = listToArray(a[0]) || [], ys = listToArray(a[1]) || []; return xs.every((x) => ys.some((y) => { const m = e.mark(); const r = e.unify(x, y); e.undo(m); return r; })); });
  // b_setval/2: a global that backtracking restores (an entry on the trail whose undo puts the old
  // value back); the value is not copied, as in SWI-Prolog
  det('b_setval/2', (a, e) => {
    const k = textOf(a[0]), had = e.globals.has(k), old = e.globals.get(k);
    e.globals.set(k, a[1]);
    e.trail.push({ set ref(_) { if (had) e.globals.set(k, old); else e.globals.delete(k); } });
    return true;
  });
  det('b_getval/2', (a, e) => { const k = textOf(a[0]); if (!e.globals.has(k)) throw existErr('variable', a[0]); return e.unify(a[1], e.globals.get(k)); });
  // arithmetic functions as predicates (abs(X, Y) is Y is abs(X)), as SWI-Prolog 9 has them
  for (const [f, n] of [['abs', 1], ['sign', 1], ['trunc', 1], ['max', 2], ['min', 2], ['truncate', 1], ['ceiling', 1], ['floor', 1], ['round', 1], ['sqrt', 1], ['sin', 1], ['cos', 1], ['tan', 1], ['asin', 1], ['acos', 1], ['atan', 1], ['log', 1], ['exp', 1], ['gcd', 2], ['msb', 1]]) if (!B[f + '/' + (n + 1)]) det(f + '/' + (n + 1), (a, e) => e.unify(a[n], P.evalArith(Cmp(f, a.slice(0, n)))));
  det('safe_goal/1', () => true); // library(sandbox): the interpreter runs programs in its own engine
  det('findnsols/4', (a, e) => {
    const n = Number(P.evalArith(a[0]).v), out = [];
    const m = e.mark();
    if (n > 0) e.solve(a[2], () => { out.push(P.copy(P.resolve(a[1]))); return out.length < n; });
    e.undo(m);
    return e.unify(a[3], list(out));
  });
  det('findnsols/5', (a, e) => {
    const n = Number(P.evalArith(a[0]).v), out = [];
    const m = e.mark();
    if (n > 0) e.solve(a[2], () => { out.push(P.copy(P.resolve(a[1]))); return out.length < n; });
    e.undo(m);
    return e.unify(a[3], list(out, a[4]));
  });
  det('term_hash/2', (a, e) => { if (!isGround(a[0])) return true; let h = 0; const s = show(a[0], { quoted: true }); for (let i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) & 0xffffff; return e.unify(a[1], Int(h)); });
  det('tab/1', (a, e) => { e.write(' '.repeat(Number(P.evalArith(a[0]).v))); return true; });

  // Library predicates written in Prolog, added to every program the interpreter runs (so the
  // converter sees them as ordinary predicates). setup_call_cleanup keeps the goal's first answer.
  P.SWI_PRELUDE = `
'$scc'(S, G, C) :- once(S), catch(G, E, true) -> ignore(C), ( var(E) -> true ; throw(E) ) ; ignore(C), fail.
convlist(_, [], []).
convlist(G, [X|Xs], Ys) :- ( call(G, X, Y) -> Ys = [Y|Ys1] ; Ys = Ys1 ), convlist(G, Xs, Ys1).
assertion(G) :- ( \\+ \\+ G -> true ; throw(error(assertion_failed(G), _)) ).
must_be(Type, X) :- '$must_be'(Type, X).
'$must_be'(_, X) :- var(X), !, throw(error(instantiation_error, _)).
'$must_be'(list, X) :- !, ( is_list(X) -> true ; throw(error(type_error(list, X), _)) ).
'$must_be'(integer, X) :- !, ( integer(X) -> true ; throw(error(type_error(integer, X), _)) ).
'$must_be'(atom, X) :- !, ( atom(X) -> true ; throw(error(type_error(atom, X), _)) ).
'$must_be'(callable, X) :- !, ( callable(X) -> true ; throw(error(type_error(callable, X), _)) ).
'$must_be'(boolean, X) :- !, ( (X == true ; X == false) -> true ; throw(error(type_error(boolean, X), _)) ).
'$must_be'(nonneg, X) :- !, ( integer(X), X >= 0 -> true ; throw(error(type_error(nonneg, X), _)) ).
'$must_be'(positive_integer, X) :- !, ( integer(X), X > 0 -> true ; throw(error(type_error(positive_integer, X), _)) ).
'$must_be'(_, _).
is_of_type(Type, X) :- catch('$must_be'(Type, X), _, fail).
max_member(P, M, L) :- L = [H|T], foldl([X, A0, A]>>( call(P, A0, X) -> A = X ; A = A0 ), T, H, M).
nb_increment(K) :- nb_getval(K, V), V1 is V + 1, nb_setval(K, V1).
option(Opt, Options, Default) :- arg(1, Opt, V), functor(Opt, N, 1), functor(G, N, 1), ( memberchk(G, Options) -> arg(1, G, V) ; memberchk(N = V0, Options) -> V = V0 ; V = Default ).
option(Opt, Options) :- functor(Opt, N, 1), arg(1, Opt, V), ( memberchk(Opt, Options) -> true ; memberchk(N = V, Options) ).
select_option(Opt, Options, Rest) :- functor(Opt, N, 1), functor(G, N, 1), select(G, Options, Rest), !, Opt = G.
select_option(Opt, Options, Rest, Default) :- ( select_option(Opt, Options, Rest) -> true ; arg(1, Opt, Default), Rest = Options ).
selectchk(X, Xs, Y, Ys) :- '$select4'(X, Xs, Y, Ys), !.
'$select4'(X, [X|T], Y, [Y|T]).
'$select4'(X, [H|T], Y, [H|T2]) :- '$select4'(X, T, Y, T2).
select(X, Xs, Y, Ys) :- '$select4'(X, Xs, Y, Ys).
same_length([], []).
same_length([_|A], [_|B]) :- same_length(A, B).
map_list_to_pairs(F, L, Ps) :- '$mltp'(L, F, Ps).
'$mltp'([], _, []).
'$mltp'([H|T], F, [K-H|Ps]) :- call(F, H, K), '$mltp'(T, F, Ps).
nth0(I, L, E, R) :- integer(I), !, I >= 0, '$nth_del'(I, L, E, R).
nth0(I, L, E, R) :- var(I), '$nth_gen'(L, E, R, 0, I).
nth1(I, L, E, R) :- integer(I), !, I0 is I - 1, nth0(I0, L, E, R).
nth1(I, L, E, R) :- nth0(I0, L, E, R), I is I0 + 1.
'$nth_del'(0, [E|R], E, R) :- !.
'$nth_del'(I, [H|T], E, [H|R]) :- I1 is I - 1, '$nth_del'(I1, T, E, R).
'$nth_gen'([E|R], E, R, B, B).
'$nth_gen'([H|T], E, [H|R], B0, B) :- B1 is B0 + 1, '$nth_gen'(T, E, R, B1, B).
empty_assoc('$assoc'([])).
get_assoc(K, '$assoc'(L), V) :- '$get_assoc'(L, K, V).
'$get_assoc'([K0-V0|T], K, V) :- compare(O, K, K0), ( O = (=) -> V = V0 ; O = (>) -> '$get_assoc'(T, K, V) ).
put_assoc(K, '$assoc'(L), V, '$assoc'(L2)) :- '$put_assoc'(L, K, V, L2).
'$put_assoc'([], K, V, [K-V]).
'$put_assoc'([K0-V0|T], K, V, L) :- compare(O, K, K0), ( O = (=) -> L = [K-V|T] ; O = (<) -> L = [K-V, K0-V0|T] ; L = [K0-V0|L1], '$put_assoc'(T, K, V, L1) ).
list_to_assoc(Ps, '$assoc'(L)) :- keysort(Ps, L).
assoc_to_list('$assoc'(L), L).
assoc_to_keys('$assoc'(L), Ks) :- pairs_keys(L, Ks).
assoc_to_values('$assoc'(L), Vs) :- pairs_values(L, Vs).
max_assoc('$assoc'(L), K, V) :- last(L, K-V).
min_assoc('$assoc'([K-V|_]), K, V).
del_assoc(K, '$assoc'(L), V, '$assoc'(L2)) :- select(K0-V, L, L2), K0 == K, !.
% plunit: the loader keeps test(Name[, Options]) :- Body between begin_tests/end_tests as '$plunit_test'/4
:- dynamic('$plunit_test'/4).
:- dynamic('$plunit_unit'/2).
begin_tests(_).
begin_tests(_, _).
end_tests(_).
run_tests :- '$run_tests'(_).
run_tests(Spec) :- is_list(Spec), !, forall(member(S, Spec), run_tests(S)).
run_tests(Spec) :- ( Spec = U:N -> true ; U = Spec ), '$run_tests'(U, N).
'$run_tests'(U) :- '$run_tests'(U, _).
'$run_tests'(U, N) :-
    findall(U-N-O-I, ( clause('$plunit_test'(U, N, O, I), _), \\+ ( '$plunit_unit'(U, UO), '$unit_skip'(UO) ) ), Ts),
    foldl('$run_test', Ts, 0-0, Pass-Fail),
    Total is Pass + Fail,
    ( Fail =:= 0 -> format(user_error, "% All ~w tests passed~n", [Total]) ; format(user_error, "% ~w tests failed~n% ~w tests passed~n", [Fail, Pass]), fail ).
'$run_test'(U-N-O0-I, P0-F0, P-F) :-
    ( is_list(O0) -> O = O0 ; O = [O0] ),
    ( ( memberchk(blocked(_), O) ; memberchk(fixme(_), O) ; memberchk(condition(C), O), \+ catch(C, _, fail) ) -> P = P0, F = F0
    ; ( memberchk(setup(S), O) -> catch(S, _, true) ; true ),
      ( catch('$test_ok'(U, N, O, I), E, ( format(user_error, "ERROR: test ~w:~w: caught exception ~q~n", [U, N, E]), fail ))
      -> P is P0 + 1, F = F0
      ;  F is F0 + 1, P = P0, format(user_error, "ERROR: test ~w:~w: failed~n", [U, N]) ),
      ( memberchk(cleanup(Cl), O) -> catch(Cl, _, true) ; true ) ).
'$test_ok'(U, N, O, I) :-
    ( memberchk(fail, O) -> \\+ '$plunit_test'(U, N, _, I)
    ; memberchk(false, O) -> \\+ '$plunit_test'(U, N, _, I)
    ; memberchk(throws(E), O) -> catch(('$plunit_test'(U, N, _, I), fail), X, subsumes_term(E, X))
    ; memberchk(error(E), O) -> catch(('$plunit_test'(U, N, _, I), fail), X, subsumes_term(error(E, _), X))
    ; memberchk(all(Cmp), O) -> Cmp =.. [Op, _, L], findall(T, ( '$plunit_test'(U, N, O1, I), '$opts'(O1, Os1), memberchk(all(C1), Os1), arg(1, C1, T) ), L1), call(Op, L1, L)
    ; memberchk(set(Cmp), O) -> Cmp =.. [Op, _, L], findall(T, ( '$plunit_test'(U, N, O1, I), '$opts'(O1, Os1), memberchk(set(C1), Os1), arg(1, C1, T) ), L0), sort(L0, L1), sort(L, L2), call(Op, L1, L2)
    ; once('$plunit_test'(U, N, O2, I)), '$opts'(O2, Os2), forall(( member(C, Os2), '$test_cond'(C, G) ), G) ).
'$unit_skip'(UO) :- '$opts'(UO, Os), ( memberchk(blocked(_), Os) ; memberchk(condition(C), Os), \\+ catch(C, _, fail) ), !.
'$opts'(O, Os) :- ( is_list(O) -> Os = O ; Os = [O] ).
'$test_cond'(true(G), G) :- !.
'$test_cond'(C, C) :- compound(C), functor(C, F, 2), memberchk(F, [==, =, =:=, =@=, \\==, \\=]).
random_permutation(L, P) :- is_list(L), !, findall(K-X, (member(X, L), random(K)), KXs), keysort(KXs, S), pairs_values(S, P).
random_permutation(L, P) :- random_permutation(P, L).
random_member(X, L) :- length(L, N), N > 0, I is random(N), nth0(I, L, X).
random_select(X, L, R) :- length(L, N), N > 0, I is random(N), nth0(I, L, X, R).
list_to_ord_set(L, S) :- sort(L, S).
ord_union(A, B, C) :- append(A, B, L), sort(L, C).
ord_union(Ls, S) :- append(Ls, L), sort(L, S).
ord_subtract(A, B, C) :- exclude([X]>>ord_memberchk(X, B), A, C).
ord_intersection(A, B, C) :- include([X]>>ord_memberchk(X, B), A, C).
ord_memberchk(X, L) :- memberchk(X, L).
ord_subset(A, B) :- forall(member(X, A), ord_memberchk(X, B)).
ord_insert(S, E, S2) :- ord_union(S, [E], S2).
ord_add_element(S, E, S2) :- ord_union(S, [E], S2).
ord_del_element(S, E, S2) :- ord_subtract(S, [E], S2).
ord_empty([]).
sumlist(L, S) :- sum_list(L, S).
nextto(X, Y, [X, Y|_]).
nextto(X, Y, [_|Zs]) :- nextto(X, Y, Zs).
partition(P, L, I, E, G) :- '$partition5'(L, P, I, E, G).
'$partition5'([], _, [], [], []).
'$partition5'([H|T], P, I, E, G) :- call(P, O, H), '$partition5_'(O, H, P, T, I, E, G).
'$partition5_'(<, H, P, T, [H|I], E, G) :- '$partition5'(T, P, I, E, G).
'$partition5_'(=, H, P, T, I, [H|E], G) :- '$partition5'(T, P, I, E, G).
'$partition5_'(>, H, P, T, I, E, [H|G]) :- '$partition5'(T, P, I, E, G).
subsumes_term(G, S) :- \\+ \\+ ( term_variables(S, V1), G = S, term_variables(V1, V2), V1 == V2 ).
`;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog converter: Prolog with cuts and choicepoints -> cut-free, choicepoint-free Detlog.
   Every goal denotes an answer packet: a list of e(EnvRow) rows and out(Text) items, in Prolog order.
   findall/aggregate_all/\+/if-then-else/once are written as packet predicates; the output contains no
   cut, ;, ->, \+, findall, call/N or nondeterministic builtin.  Each rewrite is recorded as a proof step. */
(function (P) {
  'use strict';
  const { Atom, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, listToArray, copy, termVars, show } = P;
  const D = deref;
  const conj = gs => { gs = gs.filter(g => !(D(g).t === 'a' && D(g).n === 'true')); if (!gs.length) return P.TRUE; let r = gs[gs.length - 1]; for (let i = gs.length - 2; i >= 0; i--) r = Cmp(',', [gs[i], r]); return r; };
  const flatConj = (g, out) => { out = out || []; g = D(g); if (g.t === 'c' && g.f === ',' && g.a.length === 2) { flatConj(g.a[0], out); flatConj(g.a[1], out); } else out.push(g); return out; };
  const flatDisj = (g, out) => { out = out || []; g = D(g); if (g.t === 'c' && g.f === ';' && g.a.length === 2 && !isIte(g.a[0])) { out.push(g.a[0]); flatDisj(g.a[1], out); } else out.push(g); return out; };
  function isIte(g) { g = D(g); return g.t === 'c' && g.f === '->' && g.a.length === 2; }
  const kk = g => P.key(g);
  const eq = (a, b) => Cmp('=', [a, b]);
  const E = L => Cmp('e', [L]);

  // ----- builtin classification -----
  const EFFECT = new Set(['write/1', 'print/1', 'writeln/1', 'writeq/1', 'write_canonical/1', 'write_term/2', 'nl/0', 'tab/1', 'put_char/1', 'format/1', 'format/2', 'flush_output/0']);
  const DBEFFECT = new Set(['assert/1', 'asserta/1', 'assertz/1', 'retractall/1', 'nb_setval/2', 'b_setval/2', 'setarg/3', 'nb_setarg/3']);
  const NONDET_BI = new Set(['member/2', 'between/3', 'append/3', 'length/2', 'nth0/3', 'nth1/3', 'select/3', 'permutation/2', 'atom_concat/3', 'sub_atom/5', 'sub_string/5', 'arg/3', 'last/2', 'char_type/2', 'retract/1', 'get_dict/3', 'clause/2', 'current_prolog_flag/2', 'string_concat/3']);
  const GENERATOR_BI = new Set(['member/2', 'between/3']);
  const PURE_BI = new Set(['=/2', 'is/2', '=:=/2', '=\\=/2', '</2', '>/2', '=</2', '>=/2', 'between/3', 'member/2', 'succ/2', 'plus/3', 'true/0']);
  const CONTROL = new Set([',/2', ';/2', '->/2', '\\+/1', 'findall/3', 'findall/4', 'aggregate_all/3', 'bagof/3', 'setof/3', 'true/0', 'fail/0', 'false/0', '!/0']);
  function biKind(k, g) {
    if (k === 'format/3') { const s = D(D(g).a[0]); if (s.t === 'c' && ['atom', 'string', 'codes', 'chars'].includes(s.f) && s.a.length === 1) return 'det'; return 'effect'; }
    if (EFFECT.has(k)) return 'effect';
    if (DBEFFECT.has(k)) return 'dbeffect';
    if (NONDET_BI.has(k)) return 'nondet';
    const b = P.builtins[k];
    if (b && !b.nondet && !b.call) return 'det';
    return null;
  }
  P.biKind = biKind; P.EFFECT = EFFECT; P.NONDET_BI = NONDET_BI; P.PURE_BI = PURE_BI;

  // ----- naming -----
  function cpName(f) { return f + '__cp'; }

  // ===================== conversion =====================
  // opts: { mnn: bool, s2aMax: 1000, memo: bool, splice: bool, fuse: bool, s2a: bool }
  function convert(src, opts) {
    opts = Object.assign({ mnn: false, s2aMax: 1000 }, opts || {});
    const mnn = !!opts.mnn;
    const feat = { fuse: opts.fuse !== false, // det_prefix, effect_prefix, ite_det, neg_det are detlog2's standard goal rules (plain and MNN)
      scan: opts.scan !== false, // ite_scan/neg_scan: a committed member/2 condition is a first-match scan (plain and MNN)
      factScan: mnn && opts.scan !== false, // ite_scan over a predicate of facts (MNN)
      det: mnn && opts.det !== false, // DET: output-free predicates with first-argument-exclusive clauses run without packets
      splice: mnn && opts.splice !== false, s2a: mnn && opts.s2a !== false, memo: mnn && opts.memo !== false };
    // MNN: the source rewrites first (src/rewrite.js: solve for the last generator, accumulate an appended
    // result), each derived from first principles; their derivations are in out.algebra
    let algebra = [];
    if (mnn && opts.algebra !== false && typeof src === 'string' && P.rewrite) { const rw = P.rewrite(src); src = rw.text; algebra = rw.steps; }
    const prog = typeof src === 'string' ? P.loadProgram(src) : src;
    const out = { source: src, algebra, mode: mnn ? 'mnn' : 'plain', preds: [], clauses: [], steps: [], warnings: [], errors: [], report: [], feat, specs: [], queries: [] };
    // queries become predicates '$query<i>'(V1..Vk) so that they are converted like any clause body
    const queryPreds = new Set();
    (opts.queries || []).forEach((qt, i) => {
      try {
        const q = P.readTerm(qt);
        if (mnn && opts.algebra !== false && P.fuseQuery) q.term = P.fuseQuery(prog, q.term, algebra);
        const vars = q.vars.filter(([nm]) => !nm.startsWith('_'));
        const nm = '$query' + (i + 1);
        const head = Cmp(nm, vars.map(([, v]) => v));
        const cl = prog.add(Cmp(':-', [head, q.term]), q.vars);
        queryPreds.add(nm + '/' + vars.length);
        out.queries.push({ text: qt, pred: nm, vars: vars.map(([n]) => n), key: nm + '/' + vars.length });
      } catch (e) { out.queries.push({ text: qt, error: e.message }); }
    });
    out.queryPreds = queryPreds;
    const step = (rule, pred, srcTxt, info) => { const s = { id: out.steps.length + 1, rule, pred, src: srcTxt, clauses: [], info: info || {} }; out.steps.push(s); return s; };
    const userPreds = new Set(prog.order);

    // ---- 0. normalise clauses (names, higher-order specialisation, local cuts) ----
    const specs = new Map(); // variant key -> spec pred name
    const srcPreds = new Map(); // key -> [{head, body}]
    const order = [];
    const addSrc = (k, cl) => { if (!srcPreds.has(k)) { srcPreds.set(k, []); order.push(k); } srcPreds.get(k).push(cl); };
    let specN = 0;
    function renameVars(term) {
      const vs = termVars(term); let u = 0;
      const used = new Set(vs.map(v => v.name).filter(Boolean));
      for (const v of vs) {
        if (!v.name || v.name === '_') { v.name = 'U__' + (++u); continue; }
        if (v.name.startsWith('_')) { v.name = 'U__' + v.name.slice(1); continue; }
        if (v.name.includes('__')) { const nn = v.name.replace(/__+/g, '_'); out.warnings.push({ pred: null, msg: 'variable ' + v.name + ' renamed to ' + nn + ' (`__` is reserved for generated names)' }); v.name = nn; }
      }
      return term;
    }
    function normGoal(g, ctx) {
      g = D(g);
      if (g.t === 'v') throw convErr(ctx, 'call of an unbound variable goal (call/1 of a variable) needs call/N, which Detlog does not have');
      if (g.t === 'n' || g.t === 's') throw convErr(ctx, 'goal is not callable: ' + show(g));
      const k = kk(g);
      switch (k) {
        case ',/2': return Cmp(',', [normGoal(g.a[0], ctx), normGoal(g.a[1], ctx)]);
        case ';/2': {
          const l = D(g.a[0]);
          if (l.t === 'c' && l.f === '->' && l.a.length === 2) return Cmp(';', [Cmp('->', [cutLocal(normGoal(l.a[0], ctx), ctx), normGoal(l.a[1], ctx)]), normGoal(g.a[1], ctx)]);
          if (l.t === 'c' && l.f === '*->') throw convErr(ctx, 'soft-cut *-> is not supported');
          return Cmp(';', [normGoal(g.a[0], ctx), normGoal(g.a[1], ctx)]);
        }
        case '->/2': return Cmp(';', [Cmp('->', [cutLocal(normGoal(g.a[0], ctx), ctx), normGoal(g.a[1], ctx)]), P.FAIL]);
        case '*->/2': throw convErr(ctx, 'soft-cut *-> is not supported');
        case '\\+/1': case 'not/1': rw(ctx, 'neg', g); return Cmp('\\+', [cutLocal(normGoal(g.a[0], ctx), ctx)]);
        case 'once/1': rw(ctx, 'once', g); return Cmp(';', [Cmp('->', [cutLocal(normGoal(g.a[0], ctx), ctx), P.TRUE]), P.FAIL]);
        case 'ignore/1': rw(ctx, 'ignore', g); return Cmp(';', [Cmp('->', [cutLocal(normGoal(g.a[0], ctx), ctx), P.TRUE]), P.TRUE]);
        case 'forall/2': rw(ctx, 'forall', g); return Cmp('\\+', [Cmp(',', [cutLocal(normGoal(g.a[0], ctx), ctx), Cmp('\\+', [cutLocal(normGoal(g.a[1], ctx), ctx)])])]);
        case 'call/1': { const c = D(g.a[0]); if (c.t === 'v') throw convErr(ctx, 'call/1 of an unbound variable'); rw(ctx, 'call', g); return cutLocal(normGoal(c, ctx), ctx); }
        case 'findall/3': return Cmp('findall', [g.a[0], cutLocal(normGoal(g.a[1], ctx), ctx), g.a[2]]);
        case 'findall/4': return Cmp(',', [Cmp('findall', [g.a[0], cutLocal(normGoal(g.a[1], ctx), ctx), Var('L__f')]), Cmp('append', [Var('L__f'), g.a[3], g.a[2]])]);
        case 'aggregate_all/3': return Cmp('aggregate_all', [g.a[0], cutLocal(normGoal(g.a[1], ctx), ctx), g.a[2]]);
        case 'bagof/3': case 'setof/3': {
          let gl = D(g.a[1]); const ex = [];
          while (gl.t === 'c' && gl.f === '^' && gl.a.length === 2) { termVars(gl.a[0], ex); gl = D(gl.a[1]); }
          const exS = new Set(termVars(g.a[0]).concat(ex));
          const free = termVars(gl).filter(v => !exS.has(v));
          const usedElsewhere = free.filter(v => ctx.otherVars && ctx.otherVars.has(v));
          if (usedElsewhere.length) throw convErr(ctx, g.f + '/3 groups by its free variables (' + usedElsewhere.map(v => v.name).join(', ') + '); add ^ or use findall/3');
          rw(ctx, g.f, g);
          const Lv = Var('L__b'); const goals = [Cmp('findall', [g.a[0], cutLocal(normGoal(gl, ctx), ctx), Lv]), Cmp('\\=', [Lv, NIL])];
          if (g.f === 'setof') goals.push(Cmp('sort', [Lv, g.a[2]])); else goals.push(eq(Lv, g.a[2]));
          return conj(goals);
        }
        case 'phrase/2': case 'phrase/3': { const c = D(g.a[0]); if (c.t === 'v') throw convErr(ctx, 'phrase/2 of an unbound body needs call/N'); rw(ctx, 'phrase', g); return normGoal(addArgs(c, [g.a[1], g.a.length === 3 ? g.a[2] : NIL]), ctx); }
        case 'catch/3': ctx.warn('catch/3: errors are not caught in Detlog; the goal is converted on its own'); return normGoal(g.a[0], ctx);
      }
      if (k && k.startsWith('call/') && g.a.length > 1) {
        const c = D(g.a[0]); if (c.t === 'v') throw convErr(ctx, 'call/N with an unbound closure needs call/N, which Detlog does not have');
        rw(ctx, 'call', g); return normGoal(addArgs(c, g.a.slice(1)), ctx);
      }
      const hk = higherOrder(g, ctx); if (hk) return hk;
      if (k === '!/0') return g;
      if (!userPreds.has(k) && !specs.has(k) && !CONTROL.has(k) && !biKind(k, g) && !srcPreds.has(k)) {
        if (prog.dynamic.has(k)) return g;
        throw convErr(ctx, 'unknown procedure ' + k);
      }
      return g;
    }
    function rw(ctx, kind, g) { ctx.rewrites.push({ kind, src: show(g) }); }
    function addArgs(c, extra) { c = D(c); if (c.t === 'a') return Cmp(c.n, extra); if (c.t === 'c' && c.f === '>>' && c.a.length === 2) return applyLambda(c, extra); return Cmp(c.f, c.a.concat(extra)); }
    // yall lambda  Params>>Body  applied to arguments: parameters are substituted (variables) or unified (patterns)
    function applyLambda(c, extra) {
      let params = D(c.a[0]); let body = c.a[1];
      if (params.t === 'c' && params.f === '/' && params.a.length === 2) params = D(params.a[1]);
      const ps = listToArray(params) || [];
      const map = new Map(); const goals = [];
      ps.forEach((p, i) => { if (i >= extra.length) return; const pd = D(p); if (pd.t === 'v' && !map.has(pd)) map.set(pd, extra[i]); else goals.push(eq(p, extra[i])); });
      const sub = t => { t = D(t); if (t.t === 'v') return map.has(t) ? map.get(t) : t; if (t.t === 'c') return Cmp(t.f, t.a.map(sub)); return t; };
      let g = sub(body);
      if (extra.length > ps.length) g = addArgs(g, extra.slice(ps.length));
      return conj(goals.map(sub).concat([g]));
    }
    // maplist/foldl/include/exclude/partition with a known closure -> specialised predicate (rule SPEC)
    function higherOrder(g, ctx) {
      const k = kk(g); const m = /^(maplist|foldl|include|exclude|partition)\/(\d)$/.exec(k);
      if (!m) return null;
      const kind = m[1], ar = +m[2];
      if (kind === 'maplist' && (ar < 2 || ar > 7)) return null;
      if (kind === 'foldl' && (ar < 4 || ar > 6)) return null;
      if ((kind === 'include' || kind === 'exclude') && ar !== 3) return null;
      if (kind === 'partition' && ar !== 4) return null;
      const clo = D(g.a[0]);
      if (clo.t === 'v') throw convErr(ctx, kind + '/' + ar + ' with an unbound closure needs call/N');
      let fv = termVars(clo);
      // a yall lambda: its parameters and the variables only it has are its own, fresh at each call
      // (yall copies the lambda); Free/Params>>Body shares Free; otherwise the variables the clause
      // also has outside the lambda are passed in (its inputs)
      if (clo.t === 'c' && clo.f === '>>' && clo.a.length === 2) {
        const ps = D(clo.a[0]);
        if (ps.t === 'c' && ps.f === '/' && ps.a.length === 2) { const free = new Set(termVars(ps.a[0])); fv = fv.filter((v) => free.has(v)); }
        else if (ctx.clause) {
          const count = (t, m) => { const st = [t]; while (st.length) { const x = D(st.pop()); if (x.t === 'v') m.set(x, (m.get(x) || 0) + 1); else if (x.t === 'c') for (const y of x.a) st.push(y); } return m; };
          const inC = count(ctx.clause, new Map()), inL = count(clo, new Map());
          fv = fv.filter((v) => (inC.get(v) || 0) > (inL.get(v) || 0));
        }
      }
      const cloKey = kind + ar + ':' + P.variantKey(Cmp('-', [list(fv), clo]));
      let nm = specs.get(cloKey);
      const nLists = kind === 'maplist' ? ar - 1 : kind === 'foldl' ? ar - 3 : 1;
      const cloName = P.name(clo) === '>>' ? 'lambda' : P.name(clo).replace(/[^A-Za-z0-9_]/g, '_');
      if (P.name(clo) === '>>') ctx.warn(kind + '/' + ar + ' lambda: variables of the lambda other than its parameters are shared with the clause (yall would copy unbound ones)');
      if (!nm) {
        nm = kind + '_' + cloName + '__s' + (++specN);
        specs.set(cloKey, nm);
        // build spec clauses
        const cm = new Map(); const c2 = copy(Cmp('-', [list(fv), clo]), cm); const fv2 = listToArray(c2.a[0]); const clo2 = c2.a[1];
        fv2.forEach((v, i) => { v.name = 'F' + (i + 1); });
        let cls = [];
        if (kind === 'maplist') {
          const Xs = [], Ts = [];
          for (let i = 0; i < nLists; i++) { Xs.push(Var('X' + (i + 1))); Ts.push(Var('T' + (i + 1))); }
          cls.push({ head: Cmp(nm, Array(nLists).fill(NIL).concat(fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, Xs.map((x, i) => cons(x, Ts[i])).concat(fv2)), body: Cmp(',', [addArgs(clo2, Xs), Cmp(nm, Ts.concat(fv2))]) });
        } else if (kind === 'foldl') {
          const Xs = [], Ts = []; for (let i = 0; i < nLists; i++) { Xs.push(Var('X' + (i + 1))); Ts.push(Var('T' + (i + 1))); }
          const V = Var('V'), V0 = Var('V0'), V1 = Var('V1');
          cls.push({ head: Cmp(nm, Array(nLists).fill(NIL).concat([V, V], fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, Xs.map((x, i) => cons(x, Ts[i])).concat([V0, V], fv2)), body: Cmp(',', [addArgs(clo2, Xs.concat([V0, V1])), Cmp(nm, Ts.concat([V1, V], fv2))]) });
        } else if (kind === 'include' || kind === 'exclude') {
          const X = Var('X'), T = Var('T'), R = Var('R'), R1 = Var('R1');
          const keep = eq(R, cons(X, R1)), drop = eq(R, R1);
          cls.push({ head: Cmp(nm, [NIL, NIL].concat(fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, [cons(X, T), R].concat(fv2)), body: Cmp(',', [Cmp(';', [Cmp('->', [addArgs(clo2, [X]), kind === 'include' ? keep : drop]), kind === 'include' ? drop : keep]), Cmp(nm, [T, R1].concat(fv2))]) });
        } else {
          const X = Var('X'), T = Var('T'), I = Var('I'), I1 = Var('I1'), Ex = Var('Ex'), Ex1 = Var('Ex1');
          cls.push({ head: Cmp(nm, [NIL, NIL, NIL].concat(fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, [cons(X, T), I, Ex].concat(fv2)), body: Cmp(',', [Cmp(';', [Cmp('->', [addArgs(clo2, [X]), Cmp(',', [eq(I, cons(X, I1)), eq(Ex, Ex1)])]), Cmp(',', [eq(I, I1), eq(Ex, cons(X, Ex1))])]), Cmp(nm, [T, I1, Ex1].concat(fv2))]) });
        }
        const sk = nm + '/' + (cls[0].head.a.length);
        userPreds.add(sk);
        out.specs.push({ name: nm, kind: kind + '/' + ar, closure: show(clo), key: sk });
        const st = step('SPEC', sk, show(g), { closure: show(clo), kind: kind + '/' + ar });
        for (const cl of cls) {
          const sctx = mkNormCtx(sk, cl);
          cl.body = normGoal(cl.body, sctx);
          renameVars(Cmp('-', [cl.head, cl.body]));
          addSrc(sk, { head: cl.head, body: cl.body, spec: st.id, origText: P.showClause(Cmp(':-', [cl.head, cl.body])) });
        }
      }
      const lists = kind === 'partition' ? [g.a[1], g.a[2], g.a[3]] : g.a.slice(1);
      return Cmp(nm, lists.concat(fv));
    }
    // a cut local to a goal (findall, \+, call, condition): (A, !, B) -> (A -> B' ; fail)
    function cutLocal(g, ctx) {
      const gs = flatConj(g);
      const i = gs.findIndex(x => D(x).t === 'a' && D(x).n === '!');
      if (i < 0) return g;
      rw(ctx, 'local_cut', g);
      const before = conj(gs.slice(0, i));
      const after = cutLocal(conj(gs.slice(i + 1)), ctx);
      return Cmp(';', [Cmp('->', [before, after]), P.FAIL]);
    }
    function containsNestedCut(g) {
      g = D(g);
      if (g.t !== 'c') return false;
      if (g.f === ';' && g.a.length === 2) return hasCutAnywhere(g.a[0]) || hasCutAnywhere(g.a[1]);
      if (g.f === '->' && g.a.length === 2) return hasCutAnywhere(g.a[1]);
      if (g.f === ',' && g.a.length === 2) return containsNestedCut(g.a[0]) || containsNestedCut(g.a[1]);
      return false;
    }
    function hasCutAnywhere(g) {
      g = D(g);
      if (g.t === 'a') return g.n === '!';
      if (g.t !== 'c') return false;
      if ([',', ';', '->'].includes(g.f) && g.a.length === 2) return hasCutAnywhere(g.a[0]) || hasCutAnywhere(g.a[1]);
      return false;
    }
    function hasCutAnywhereDeep(g) {
      g = D(g);
      if (g.t === 'a') return g.n === '!';
      if (g.t !== 'c') return false;
      if ([',', ';', '->'].includes(g.f) && g.a.length === 2) return hasCutAnywhereDeep(g.a[0]) || hasCutAnywhereDeep(g.a[1]);
      if (g.f === '\\+' && g.a.length === 1) return hasCutAnywhereDeep(g.a[0]);
      if ((g.f === 'findall' || g.f === 'aggregate_all') && g.a.length === 3) return hasCutAnywhereDeep(g.a[1]);
      return false;
    }
    function convErr(ctx, msg) { const e = new Error((ctx && ctx.pred ? ctx.pred + ': ' : '') + msg); e.conv = true; e.pred = ctx && ctx.pred; return e; }
    function mkNormCtx(pred, cl) {
      const ctx = { pred, rewrites: [], warn: m => out.warnings.push({ pred, msg: m }), clause: Cmp(':-', [cl.head, cl.body]) };
      // variables that occur outside bagof/setof goals (for the free-variable check)
      ctx.otherVars = new Set(termVars(cl.head));
      for (const g of flatConj(cl.body)) { const gd = D(g); if (!(gd.t === 'c' && (gd.f === 'bagof' || gd.f === 'setof'))) termVars(gd).forEach(v => ctx.otherVars.add(v)); else termVars(gd.a[2]).forEach(v => ctx.otherVars.add(v)); }
      return ctx;
    }

    for (const k of prog.order) {
      for (const cl of prog.preds.get(k)) {
        const m = new Map();
        const c = copy(Cmp(':-', [cl.head, cl.body]), m);
        // restore names from reader
        if (cl.vars) for (const [nm, v] of cl.vars) { const nv = m.get(v); if (nv) nv.name = nm; }
        const origText = P.showClause(c);
        const ctx = mkNormCtx(k, { head: c.a[0], body: c.a[1] });
        try {
          const body = normGoal(c.a[1], ctx);
          renameVars(Cmp('-', [c.a[0], body]));
          addSrc(k, { head: D(c.a[0]), body, rewrites: ctx.rewrites, origText });
        } catch (e) {
          if (!e.conv) throw e;
          out.errors.push({ pred: k, msg: e.message });
          addSrc(k, { head: D(c.a[0]), body: c.a[1], error: e.message, origText });
        }
      }
    }
    for (const k of prog.dynamic) if (!srcPreds.has(k)) { addSrc(k, null); srcPreds.set(k, []); }

    // ---- 1. analysis: calls, purity, output, recursion ----
    const info = new Map();
    for (const k of order) {
      const cls = srcPreds.get(k).filter(Boolean);
      const calls = new Set(); let impure = false; let writes = false; let cut = false; let facts = true; let maxSelf = 0; let err = false; let dyn = prog.dynamic.has(k);
      for (const cl of cls) {
        if (cl.error) err = true;
        const b = D(cl.body); if (!(b.t === 'a' && b.n === 'true')) facts = false;
        let selfCalls = 0;
        (function walk(g) {
          g = D(g); const gk = kk(g);
          if (gk === ',/2' || gk === ';/2') { walk(g.a[0]); walk(g.a[1]); return; }
          if (gk === '->/2') { impure = true; walk(g.a[0]); walk(g.a[1]); return; }
          if (gk === '\\+/1') { impure = true; walk(g.a[0]); return; }
          if (gk === 'findall/3' || gk === 'aggregate_all/3') { impure = true; walk(g.a[1]); return; }
          if (gk === '!/0') { cut = true; impure = true; return; }
          if (userPreds.has(gk) || srcPreds.has(gk)) { calls.add(gk); if (gk === k) selfCalls++; return; }
          const bk = biKind(gk, g);
          if (bk === 'effect') { writes = true; impure = true; return; }
          if (bk === 'dbeffect' || gk === 'retract/1') { impure = true; writes = true; return; }
          if (!PURE_BI.has(gk)) impure = true;
        })(cl.body);
        maxSelf = Math.max(maxSelf, selfCalls);
      }
      if (dyn) impure = true;
      info.set(k, { calls, impure, writesLocal: writes, cut, facts: facts && cls.length > 0, nclauses: cls.length, maxSelf, err, dyn });
    }
    // transitive purity / output (greatest fixpoint for purity)
    let changed = true;
    for (const [, inf] of info) { inf.pure = !inf.impure && !inf.err; inf.writes = inf.writesLocal; }
    while (changed) {
      changed = false;
      for (const [k, inf] of info) {
        for (const c of inf.calls) {
          const ci = info.get(c);
          if (!ci) continue;
          if (inf.pure && !ci.pure) { inf.pure = false; changed = true; }
          if (!inf.writes && ci.writes) { inf.writes = true; changed = true; }
        }
      }
    }
    // recursion: SCCs
    const sccOf = sccs(order, k => [...(info.get(k) || { calls: [] }).calls].filter(c => info.has(c)));
    for (const k of order) {
      const inf = info.get(k); const comp = sccOf.get(k);
      inf.recursive = comp.size > 1 || inf.calls.has(k);
      // tree recursion: some clause calls predicates of its own SCC twice or more
      let tree = false;
      for (const cl of srcPreds.get(k).filter(Boolean)) { let n = 0; (function walk(g) { g = D(g); const gk = kk(g); if (gk === ',/2' || gk === ';/2' || gk === '->/2') { walk(g.a[0]); walk(g.a[1]); return; } if (comp.has(gk)) n++; })(cl.body); if (n >= 2) tree = true; }
      inf.tree = tree;
    }
    out.info = info;

    // ---- 2. per predicate code generation ----
    const genPreds = []; // {name, arity, clauses:[term], kind, src}
    const emit = (st, term, predName) => { const cl = { term: P.copy(term), step: st.id, pred: predName }; restoreNames(term, cl.term); out.clauses.push(cl); st.clauses.push(out.clauses.length - 1); return cl; };
    function restoreNames(a, b) { /* copy keeps names already */ }

    const s2aDone = new Map();
    // S2A tables are computed once: the DET analysis needs to know which predicates become loops
    const s2aCache = new Map();
    const s2aOf = (k, f, n) => { if (!s2aCache.has(k)) s2aCache.set(k, s2aTable(prog, f, n, opts.s2aMax || 1000)); return s2aCache.get(k); };
    const detPlan = feat.det ? planDet() : new Map();
    const factRowsUsed = new Set(); // facts predicates scanned by ite_scan: their table p__rows/1 is emitted
    out.ir = new Map(); // the cut-free source the Detlog interpreter runs: normalised clauses, rule CUT applied
    for (const k of order) {
      const cls = srcPreds.get(k).filter(Boolean);
      const [f, nStr] = splitKey(k); const n = +nStr;
      const inf = info.get(k);
      {
        const err = cls.find(c => c.error);
        const topCut = cls.some(c => flatConj(c.body).some(g => D(g).t === 'a' && D(g).n === '!'));
        let irc = cls;
        if (!err && topCut) { const IA = []; for (let i = 0; i < n; i++) IA.push(Var('A__' + (i + 1))); irc = [cutElim(f, n, cls, IA)]; }
        out.ir.set(k, { clauses: err ? [] : irc.map(c => ({ head: c.head, body: c.body })), error: err ? err.error : null, dynamic: !!(inf && inf.dyn) });
      }
      const A = []; for (let i = 0; i < n; i++) A.push(Var('A__' + (i + 1)));
      const Rows = Var('R__0');
      const headCp = Cmp(cpName(f), A.concat([Rows]));
      const predOut = { key: k, name: f, arity: n, cpName: cpName(f) + '/' + (n + 1), kind: null, notes: [] };
      genPreds.push(predOut);
      if (cls.some(c => c.error)) {
        predOut.kind = 'error';
        const st = step('UNSUPPORTED', k, cls.map(c => c.origText).join('\n'), { reason: cls.find(c => c.error).error });
        emit(st, Cmp(':-', [headCp, Cmp('detlog_unsupported', [Cmp('/', [Atom(f), Int(n)]), Str(cls.find(c => c.error).error)])]), k);
        predOut.notes.push('not converted: ' + cls.find(c => c.error).error);
        continue;
      }
      if (!cls.length) { // dynamic, no clauses
        predOut.kind = 'empty';
        const st = step('FACTS', k, '(no clauses)', {});
        emit(st, Cmp(':-', [headCp, eq(Rows, NIL)]), k);
        if (inf.dyn) out.warnings.push({ pred: k, msg: 'dynamic predicate: clauses asserted at run time are not seen by the converted code' });
        continue;
      }
      // --- MNN S2A unfold ---
      if (feat.s2a && inf.pure && n > 0 && !queryPreds.has(k)) {
        const tab = s2aOf(k, f, n);
        if (tab.ok) {
          const spec = s2aSpec(tab.rows, n);
          predOut.kind = 's2a';
          const st = step('S2A', k, cls.map(c => c.origText).join('\n'), { rows: tab.rows.length, spec: show(spec), formula: s2aFormula(spec) });
          emit(st, Cmp(':-', [headCp, Cmp('s2a_rows', [spec, list(A), Rows])]), k);
          predOut.notes.push('unfolded: ' + tab.rows.length + ' rows; S2A loop ' + s2aFormula(spec));
          out.report.push('unfolded ' + k + ': ' + tab.rows.length + ' rows; S2A loop for I = 0..' + (tab.rows.length - 1) + ': ' + s2aFormula(spec));
          continue;
        } else if (inf.pure) predOut.notes.push('kept (not unfolded): ' + tab.why);
      } else if (feat.s2a && n > 0 && !queryPreds.has(k)) predOut.notes.push('kept (not unfolded): not pure');
      // --- FACTS ---
      const hasCut = cls.some(c => flatConj(c.body).some(g => D(g).t === 'a' && D(g).n === '!'));
      let memoWrap = feat.memo && inf.pure && inf.tree && n > 0 && !queryPreds.has(k);
      const detForms = detPlan.get(k);
      // MEMO and DET together: p__cp tables, p__cpc is the DET wrapper, p__cpx the packet code
      const target = detForms ? Cmp(f + '__cpx', A.concat([Rows])) : memoWrap ? Cmp(f + '__cpc', A.concat([Rows])) : headCp;
      if (detForms) { genDet(k, f, n, detForms, cls, memoWrap ? f + '__cpc' : cpName(f)); predOut.kind = 'det-mode'; predOut.notes.push('deterministic mode (DET): runs without packets when its index argument selects one clause'); }
      if (memoWrap) {
        predOut.kind = 'memo';
        const Fd = Var('F__1'), R0 = Var('R__9');
        const st = step('MEMO', k, cls.map(c => c.origText).join('\n'), { reason: 'pure and tree-recursive: variant calls give the same packet' });
        emit(st, Cmp(':-', [headCp, conj([Cmp('memo_lookup', [Cmp('/', [Atom(f), Int(n)]), list(A), Fd]), Cmp(f + '__memo', [Fd].concat(A, [Rows]))])]), k);
        emit(st, Cmp(':-', [Cmp(f + '__memo', [Cmp('found', [R0])].concat(A.map(() => Var('_')), [Rows])), eq(Rows, R0)]), k);
        emit(st, Cmp(':-', [Cmp(f + '__memo', [Atom('none')].concat(A, [Rows])), conj([Cmp(f + '__cpc', A.concat([Rows])), Cmp('memo_store', [Cmp('/', [Atom(f), Int(n)]), list(A), Rows])])]), k);
        predOut.notes.push('memoised (variant tabling of a pure tree-recursive predicate)');
      }
      if (inf.facts && !hasCut) {
        if (!predOut.kind) predOut.kind = 'facts';
        const rows = cls.map(c => E(list(c.head.t === 'c' ? c.head.a : [])));
        const st = step('FACTS', k, cls.map(c => c.origText).join('\n'), { n: cls.length });
        emit(st, Cmp(':-', [target, Cmp('cp_filter', [list(rows), list(A), Rows])]), k);
        continue;
      }
      // --- CUT elimination ---
      let work = cls;
      if (hasCut) {
        const merged = cutElim(f, n, cls, A);
        const st = step('CUT', k, cls.map(c => c.origText).join('\n'), { produced: P.showClause(Cmp(':-', [merged.head, merged.body]), { varName: v => v.name }) });
        st.clauses = []; out.cutForms = out.cutForms || {}; out.cutForms[k] = P.showClause(Cmp(':-', [merged.head, merged.body]));
        work = [merged];
        if (!predOut.kind) predOut.kind = 'cut';
      }
      if (!predOut.kind) predOut.kind = cls.length > 1 ? 'choice' : 'det';
      // --- PRED + CLAUSE ---
      if (work.length === 1) {
        genClausePacket(work[0], target, A, Rows, k, f + '__c1', true);
      } else {
        const Rs = work.map((c, i) => Var('R__' + (i + 1)));
        const st = step('PRED', k, work.map(c => c.origText || '').join('\n'), { n: work.length });
        const marks = work.some(c => hasCutAnywhereDeep(c.body));
        emit(st, Cmp(':-', [target, conj(work.map((c, i) => Cmp(f + '__c' + (i + 1), A.concat([Rs[i]]))).concat([Cmp(marks ? 'rows_cut_concat' : 'rows_concat', [list(Rs), Rows])]))]), k);
        work.forEach((c, i) => { const Ri = Var('R__0'); genClausePacket(c, Cmp(f + '__c' + (i + 1), A.concat([Ri])), A, Ri, k, f + '__c' + (i + 1), false); });
      }
    }

    // ----- DET: deterministic mode -----
    // A predicate qualifies when it writes nothing, is not dynamic, is not tabled (MEMO) or unfolded (S2A),
    // its clauses (after rule CUT) are one clause or are told apart by distinct non-variable first arguments,
    // and every body goal is true/fail, a deterministic builtin, a call of a qualifying predicate, or
    // ( C -> T ; F ) / \+ C with C a conjunction of deterministic builtins.  Greatest fixpoint over calls.
    function planDet() {
      const cand = new Map();
      for (const k of order) {
        const inf = info.get(k); const cls = srcPreds.get(k).filter(Boolean);
        if (!inf || queryPreds.has(k) || inf.err || inf.dyn || inf.writes || !cls.length || cls.some(c => c.error)) continue;
        const [f, nS] = splitKey(k); const n = +nS;
        const memo = feat.memo && inf.pure && inf.tree && n > 0;
        if (!memo && feat.s2a && inf.pure && n > 0 && s2aOf(k, f, n).ok) continue;
        const topCut = cls.some(c => flatConj(c.body).some(g => D(g).t === 'a' && D(g).n === '!'));
        let forms = cls;
        if (topCut) { const IA = []; for (let i = 0; i < n; i++) IA.push(Var('A__' + (i + 1))); forms = [cutElim(f, n, cls, IA)]; }
        // the index argument: the first position where every clause has a distinct non-variable key
        let ix = 0;
        if (forms.length > 1) {
          if (!n) continue;
          ix = -1;
          for (let j = 0; j < n && ix < 0; j++) {
            const keys = forms.map(c => firstKey(D(c.head).a[j]));
            if (!keys.some(x => x === null) && new Set(keys).size === keys.length) ix = j;
          }
          // guarded: one clause with a variable there, whose body starts with integer comparisons on that
          // variable that fail for every other clause's (integer) key, as fib(N, F) :- N > 1, ... does
          let guarded = -1;
          for (let j = 0; j < n && ix < 0; j++) {
            const keys = forms.map(c => firstKey(D(c.head).a[j]));
            const vi = keys.map((x, i) => x === null ? i : -1).filter(i => i >= 0);
            const ks = keys.filter(x => x !== null);
            if (vi.length !== 1 || new Set(ks).size !== ks.length || !ks.every(x => /^n-?\d+$/.test(x))) continue;
            const vc = forms[vi[0]], hv = D(D(vc.head).a[j]);
            const guards = [];
            for (const g of flatConj(vc.body)) { const gd = D(g); if (GUARDS()[kk(gd)] && termVars(gd).every(v => v === hv) && termVars(gd).length) guards.push(gd); else break; }
            const fails = v => guards.some(gd => { const a = evalGuard(gd.a[0], hv, v), b = evalGuard(gd.a[1], hv, v); return a !== null && b !== null && !GUARDS()[kk(gd)](a, b); });
            if (guards.length && ks.every(x => fails(+x.slice(1)))) { ix = j; guarded = vi[0]; }
          }
          if (ix < 0) continue;
          forms = forms.slice(); forms.guarded = guarded;
        } else forms = forms.slice();
        forms.ix = ix; forms.memo = memo;
        cand.set(k, forms);
      }
      let changed = true;
      while (changed) {
        changed = false;
        for (const [k, forms] of cand) if (!forms.every(c => detGoalOK(c.body, cand))) { cand.delete(k); changed = true; }
      }
      return cand;
    }
    function GUARDS() { return GUARDS.m || (GUARDS.m = { '>/2': (a, b) => a > b, '</2': (a, b) => a < b, '>=/2': (a, b) => a >= b, '=</2': (a, b) => a <= b, '=:=/2': (a, b) => a === b, '=\\=/2': (a, b) => a !== b }); }
    function evalGuard(t, hv, v) { t = D(t); if (t === hv) return v; if (t.t === 'n' && !t.f) return t.v; if (t.t === 'c' && t.a.length === 2 && '+-*'.includes(t.f) && t.f.length === 1) { const a = evalGuard(t.a[0], hv, v), b = evalGuard(t.a[1], hv, v); if (a === null || b === null) return null; return t.f === '+' ? a + b : t.f === '-' ? a - b : a * b; } return null; }
    function firstKey(t) { t = D(t); if (t.t === 'v') return null; if (t.t === 'c') return 'c' + t.f + '/' + t.a.length; if (t.t === 'a') return 'a' + t.n; if (t.t === 'n') return 'n' + t.v + (t.f ? 'f' : ''); if (t.t === 's') return 's' + t.v; return null; }
    function detGoalOK(g, cand) {
      g = D(g); const k = kk(g);
      if (k === 'true/0' || k === 'fail/0' || k === 'false/0') return true;
      if (k === ',/2') return detGoalOK(g.a[0], cand) && detGoalOK(g.a[1], cand);
      if (k === ';/2') { const l = D(g.a[0]); return isIte(l) && detGoalOK(l.a[0], cand) && detGoalOK(l.a[1], cand) && detGoalOK(g.a[1], cand); }
      if (k === '\\+/1') return detGoalOK(g.a[0], cand);
      if (userPreds.has(k) || srcPreds.has(k)) return cand.has(k);
      return isDetBi(g);
    }
    // p__cp(A.., Rows) :- copy_term(A, B), p__d(B.., S), p__dr(S, B.., A.., Rows).
    // p__dr(yes, B.., _, [e(B)]).  p__dr(no, _, _, []).  p__dr(maybe, _, A.., Rows) :- p__cpx(A.., Rows).
    // p__d(X.., S): Prolog's own clause selection and body, with status yes (one answer), no (none) or
    // maybe (a first argument was unbound where several clauses could match: the packet code decides).
    function genDet(k, f, n, forms, cls, wrapName) {
      const ix = forms.ix || 0;
      const st = step('DET', k, cls.map(c => c.origText).join('\n'), { clauses: forms.length, index: ix + 1, guarded: forms.guarded >= 0, memo: !!forms.memo });
      const mk = (p) => { const a = []; for (let i = 0; i < n; i++) a.push(Var(p + '__' + (i + 1))); return a; };
      const A = mk('A'), B = mk('B'), X = mk('X'), U = () => mk('_').map(() => Var('_'));
      const S = Var('S__0'), Rows = Var('R__0');
      const dn = f + '__d', dr = f + '__dr';
      emit(st, Cmp(':-', [Cmp(wrapName, A.concat([Rows])), conj([Cmp('copy_term', [list(A), list(B)]), Cmp(dn, B.concat([S])), Cmp(dr, [S].concat(B, A, [Rows]))])]), k);
      if (forms.memo) {
        // q__dm(X.., S): a tabled call, as a status: its packet (from the table) has no row, one row or more
        //   q__dm(X.., S) :- q__cp(X.., P), q__dms(P, X.., S).
        //   q__dms([], _.., no).   q__dms([R|Rs], X.., S) :- q__dms1(Rs, R, X.., S).
        //   q__dms1([], e(Vs), X.., S) :- if_commit([X..] = Vs, S = yes, S = no).   q__dms1([_|_], _, _.., maybe).
        const Pm = Var('P__1'), Rr = Var('R__1'), Rs = Var('R__2'), Vs = Var('V__1');
        emit(st, Cmp(':-', [Cmp(f + '__dm', X.concat([S])), conj([Cmp(cpName(f), X.concat([Pm])), Cmp(f + '__dms', [Pm].concat(X, [S]))])]), k);
        emit(st, Cmp(f + '__dms', [NIL].concat(U(), [Atom('no')])), k);
        emit(st, Cmp(':-', [Cmp(f + '__dms', [cons(Rr, Rs)].concat(X, [S])), Cmp(f + '__dms1', [Rs, Rr].concat(X, [S]))]), k);
        emit(st, Cmp(':-', [Cmp(f + '__dms1', [NIL, E(Vs)].concat(X, [S])), Cmp('if_commit', [eq(list(X), Vs), eq(S, Atom('yes')), eq(S, Atom('no'))])]), k);
        emit(st, Cmp(f + '__dms1', [cons(Var('_'), Var('_')), Var('_')].concat(U(), [Atom('maybe')])), k);
      }
      emit(st, Cmp(dr, [Atom('yes')].concat(B, U(), [list([E(list(B))])])), k);
      emit(st, Cmp(dr, [Atom('no')].concat(U(), U(), [NIL])), k);
      emit(st, Cmp(':-', [Cmp(dr, [Atom('maybe')].concat(U(), A, [Rows])), Cmp(f + '__cpx', A.concat([Rows]))]), k);
      const ctx = { n: 0 };
      const clauseCode = (c, i) => {
        const cc = copy(Cmp(':-', [c.head, c.body]));
        for (const v of termVars(cc)) v.name = (v.name && v.name !== '_' ? v.name.replace(/__+/g, '_') : 'V') + '__d' + (i + 1);
        const h = D(cc.a[0]); const hargs = h.t === 'c' ? h.a.slice() : [];
        const first = hargs[ix];
        // a head argument that is a variable seen for the first time is the argument itself: no unification
        const seen = new Set(termVars(forms.length > 1 && n ? first : NIL));
        const rest = [];
        hargs.forEach((x, j) => {
          if (j === ix && forms.length > 1) return;
          const xd = D(x);
          if (xd.t === 'v' && !seen.has(xd)) { seen.add(xd); seen.add(X[j]); xd.ref = X[j]; return; }
          termVars(xd).forEach(v => seen.add(v));
          rest.push(eq(X[j], x));
        });
        const body = detSeq(flatConj(P.resolve(cc.a[1])).map(g => P.resolve(g)), S, ctx);
        const restR = rest.map(r => P.resolve(r));
        return { first: first && P.resolve(first), code: restR.length ? Cmp('if_commit', [conj(restR), body, eq(S, Atom('no'))]) : body };
      };
      const codes = forms.map(clauseCode);
      let body;
      if (forms.length === 1) body = codes[0].code;
      else {
        let chain = eq(S, Atom('no'));
        const g = forms.guarded >= 0 ? forms.guarded : -1;
        // the guarded clause matches any value its guard admits, which excludes every key: it comes last
        if (g >= 0) chain = Cmp('if_commit', [eq(X[ix], codes[g].first), codes[g].code, chain]);
        for (let i = codes.length - 1; i >= 0; i--) if (i !== g) chain = Cmp('if_commit', [eq(X[ix], codes[i].first), codes[i].code, chain]);
        body = Cmp('if_commit', [Cmp('var', [X[ix]]), eq(S, Atom('maybe')), chain]);
      }
      emit(st, Cmp(':-', [Cmp(dn, X.concat([S])), body]), k);
    }
    function detSeq(gs, S, ctx) {
      if (!gs.length) return eq(S, Atom('yes'));
      const g = D(gs[0]), rest = gs.slice(1), k = kk(g);
      if (k === 'true/0') return detSeq(rest, S, ctx);
      if (k === 'fail/0' || k === 'false/0') return eq(S, Atom('no'));
      if (k === ',/2') return detSeq(flatConj(g).concat(rest), S, ctx);
      // a condition of deterministic builtins is an if_commit/3 condition as it stands; any other deterministic
      // condition runs with its own status Sc inside the condition: no fails it (undoing its bindings),
      // yes commits, maybe abandons the deterministic attempt
      const condOf = (C, yesCode, noCode, S1) => {
        if (flatConj(C).every(isDetBi)) return Cmp('if_commit', [C, yesCode, noCode]);
        const Sc = Var('S__' + (++ctx.n));
        return Cmp('if_commit', [conj([detSeq(flatConj(C), Sc, ctx), Cmp('\\==', [Sc, Atom('no')])]), Cmp('if_commit', [eq(Sc, Atom('yes')), yesCode, eq(S1, Atom('maybe'))]), noCode]);
      };
      if (k === ';/2') {
        const C = D(g.a[0]).a[0], T = D(g.a[0]).a[1], F = g.a[1];
        if (!rest.length) return condOf(C, detSeq(flatConj(T), S, ctx), detSeq(flatConj(F), S, ctx), S);
        const S2 = Var('S__' + (++ctx.n));
        return conj([condOf(C, detSeq(flatConj(T), S2, ctx), detSeq(flatConj(F), S2, ctx), S2), Cmp('if_commit', [eq(S2, Atom('yes')), detSeq(rest, S, ctx), eq(S, S2)])]);
      }
      if (k === '\\+/1') return condOf(g.a[0], eq(S, Atom('no')), detSeq(rest, S, ctx), S);
      if (userPreds.has(k) || srcPreds.has(k)) {
        const as = g.t === 'c' ? g.a : [];
        const dname = P.name(g) + (detPlan.has(k) && detPlan.get(k).memo ? '__dm' : '__d');
        if (!rest.length) return Cmp(dname, as.concat([S]));
        const S1 = Var('S__' + (++ctx.n));
        return conj([Cmp(dname, as.concat([S1])), Cmp('if_commit', [eq(S1, Atom('yes')), detSeq(rest, S, ctx), eq(S, S1)])]);
      }
      return Cmp('if_commit', [g, detSeq(rest, S, ctx), eq(S, Atom('no'))]);
    }

    function cutElim(f, n, cls, A) {
      // single clause  p(A1..An) :- D1
      let next = P.FAIL;
      for (let i = cls.length - 1; i >= 0; i--) {
        const m = new Map();
        const c = copy(Cmp(':-', [cls[i].head, cls[i].body]), m);
        for (const v of termVars(c)) v.name = v.name + '__c' + (i + 1);
        const h = D(c.a[0]); const hargs = h.t === 'c' ? h.a : [];
        const unif = n ? eq(list(A), list(hargs)) : P.TRUE;
        const gs = flatConj(c.a[1]);
        const ci = gs.findIndex(x => D(x).t === 'a' && D(x).n === '!');
        if (ci >= 0) {
          const cond = conj([unif].concat(gs.slice(0, ci)));
          const after = laterCuts(gs.slice(ci + 1));
          next = Cmp(';', [Cmp('->', [cond, after]), next]);
        } else {
          const body = conj([unif].concat(gs));
          next = (D(next).t === 'a' && D(next).n === 'fail') ? body : Cmp(';', [body, next]);
        }
      }
      return { head: Cmp(f, A), body: next, origText: null, merged: true };
    }
    function laterCuts(gs) {
      const ci = gs.findIndex(x => D(x).t === 'a' && D(x).n === '!');
      if (ci < 0) return conj(gs);
      return Cmp(';', [Cmp('->', [conj(gs.slice(0, ci)), laterCuts(gs.slice(ci + 1))]), P.FAIL]);
    }

    // ----- clause packet -----
    function genClausePacket(cl, target, A, Rows, k, pfx, single) {
      const ctx = { pfx, n: 0, aux: 0, k, marks: hasCutAnywhereDeep(cl.body) };
      const m = new Map();
      const c = copy(Cmp(':-', [cl.head, cl.body]), m);
      const head = D(c.a[0]); const body = c.a[1];
      const hargs = head.t === 'c' ? head.a : [];
      if (cl.merged) hargs.forEach((h, i) => { const hv = D(h); if (hv.t === 'v') hv.name = 'H__' + (i + 1); });
      const Vs = termVars(Cmp('-', [head, body]));
      ctx.L = list(Vs);
      const distinctVars = hargs.every((h, i) => { const hv = D(h); return hv.t === 'v' && hargs.findIndex(x => D(x) === hv) === i; });
      // MNN: when the environment is exactly the head arguments, projecting the rows on the head renames them
      // only: the rows are the packet (rule CLAUSE with identity projection)
      const identity = (feat.det || feat.splice) && !ctx.marks && distinctVars && hargs.length === Vs.length && hargs.every((h, i) => D(h) === Vs[i]);
      const st = step('CLAUSE', k, cl.origText || P.showClause(Cmp(':-', [cl.head, cl.body])), { single, vars: Vs.map(v => v.name), identity });
      // MNN call-through:  h(V1..Vn) :- q(V1..Vn)  with distinct variables has q's packet
      const bg = D(body);
      if (identity && single && (userPreds.has(kk(bg)) || srcPreds.has(kk(bg))) && bg.t === 'c' && bg.a.length === hargs.length && bg.a.every((x, i) => D(x) === Vs[i]) && !(feat.det && detPlan.has(kk(bg)) && false)) {
        st.info.callThrough = true;
        emit(st, Cmp(':-', [Cmp(P.name(target), A.concat([Rows])), Cmp(cpName(P.name(bg)), A.concat([Rows]))]), k);
        return;
      }
      const R0 = identity ? Rows : fresh(ctx, 'R');
      const code = genGoal(body, ctx.L, R0, ctx);
      // rename the call apart and unify it with the head (resolution), then project the env rows on the head
      let proj = identity ? [] : [Cmp('project_rows', [R0, ctx.L, list(hargs), Rows])];
      if (ctx.marks && single) { const R9 = fresh(ctx, 'R'); proj = [Cmp('project_rows', [R0, ctx.L, list(hargs), R9]), Cmp('strip_cut', [R9, Rows])]; }
      // when the head arguments are distinct variables the renaming always succeeds: no decision is needed
      const rename = Cmp('copy_term', [list(A), list(hargs)]);
      const clauseBody = distinctVars ? conj([rename].concat(code, proj)) : Cmp('if_commit', [rename, conj(code.concat(proj)), eq(Rows, NIL)]);
      emit(st, Cmp(':-', [Cmp(P.name(target), A.concat([Rows])), clauseBody]), k);
      for (const ax of ctx.auxList || []) emit(ax.st, ax.term, k);
    }
    function fresh(ctx, p) { return Var(p + '__' + (++ctx.n)); }
    function auxName(ctx, kind) { return ctx.pfx + '_' + kind + (++ctx.aux); }
    function addAux(ctx, st, term) { (ctx.auxList = ctx.auxList || []).push({ st, term }); }
    // add a group of aux clauses before those of the auxiliaries generated inside them (keeps predicates contiguous, outer first)
    function insertAux(ctx, st, terms) {
      ctx.auxList = ctx.auxList || [];
      const at = ctx.auxMark !== undefined ? ctx.auxMark : ctx.auxList.length;
      for (const t of terms) ctx.auxList.push({ st, term: t });
    }

    // genGoal returns list of Detlog goals computing packet O of goal g in env L
    function genGoal(g, L, O, ctx) {
      g = D(g); const k = kk(g);
      switch (k) {
        case 'true/0': step('true', ctx.k, 'true'); return [eq(O, list([E(L)]))];
        case 'fail/0': case 'false/0': step('fail', ctx.k, 'fail'); return [eq(O, NIL)];
        case ',/2': return genConj(flatConj(g), L, O, ctx);
        case ';/2': {
          const l = D(g.a[0]);
          if (l.t === 'c' && l.f === '->' && l.a.length === 2) return genIte(l.a[0], l.a[1], g.a[1], L, O, ctx, g);
          return genDisj(flatDisj(g), L, O, ctx, g);
        }
        case '\\+/1': return genIte(g.a[0], P.FAIL, P.TRUE, L, O, ctx, g, 'neg');
        case 'findall/3': return genFindall(g, L, O, ctx, null);
        case 'aggregate_all/3': return genFindall(Cmp('findall', [aggTemplate(g.a[0]), g.a[1], Var('T__a')]), L, O, ctx, g);
        case '!/0': step('cut_mark', ctx.k, '!'); ctx.usedMarks = true; return [eq(O, list([Atom('cut'), E(L)]))];
      }
      if (userPreds.has(k) || srcPreds.has(k)) {
        const as = g.t === 'c' ? g.a : [];
        const Pk = fresh(ctx, 'P');
        const packetCall = [Cmp(cpName(P.name(g)), as.concat([Pk])), Cmp('splice_extend', [Pk, list(as), E(L), O])];
        // MNN DET-call: a deterministic-mode callee binds the environment in place; status maybe undoes that and
        // runs the packet call
        if (feat.det && detPlan.has(k) && !(feat.memo && info.get(k) && info.get(k).pure && info.get(k).tree)) {
          step('call_det', ctx.k, show(g));
          const S = fresh(ctx, 'S');
          return [Cmp('if_commit', [conj([Cmp(P.name(g) + '__d', as.concat([S])), Cmp('\\==', [S, Atom('maybe')])]),
            Cmp('if_commit', [eq(S, Atom('yes')), eq(O, list([E(L)])), eq(O, NIL)]), conj(packetCall)])];
        }
        step('call', ctx.k, show(g));
        return packetCall;
      }
      const bk = biKind(k, g);
      if (bk === 'effect' || bk === 'dbeffect') {
        if (bk === 'dbeffect') out.warnings.push({ pred: ctx.k, msg: show(g) + ': database update runs while the packet is built, in Prolog order; code that later cuts away answers may update more than Prolog would' });
        step('effect', ctx.k, show(g));
        const T = fresh(ctx, 'T');
        if (bk === 'dbeffect') return [Cmp('if_commit', [g, eq(O, list([E(L)])), eq(O, NIL)])];
        return [Cmp('effect_text', [g, T]), eq(O, list([Cmp('out', [T]), E(L)]))];
      }
      if (bk === 'nondet') {
        if (GENERATOR_BI.has(k)) step(k === 'member/2' ? 'member_cp' : 'between_cp', ctx.k, show(g)); else step('builtin_rows', ctx.k, show(g));
        if (k === 'retract/1') out.warnings.push({ pred: ctx.k, msg: 'retract/1 removes every matching clause while the packet is built' });
        const Pk = fresh(ctx, 'P');
        return [Cmp('builtin_rows', [g, Pk]), Cmp('splice_extend', [Pk, list([g]), E(L), O])];
      }
      if (bk === 'det') { step('det', ctx.k, show(g)); return [Cmp('if_commit', [g, eq(O, list([E(L)])), eq(O, NIL)])]; }
      throw convErr({ pred: ctx.k }, 'unknown procedure ' + k);
    }
    function aggTemplate(spec) { spec = D(spec); if (spec.t === 'a' && spec.n === 'count') return P.TRUE; if (spec.t === 'c' && spec.a.length === 1) return spec.a[0]; return P.TRUE; }
    function isDetBi(g) { g = D(g); const k = kk(g); if (k === 'true/0') return true; return biKind(k, g) === 'det'; }
    function isEffect(g) { g = D(g); return biKind(kk(g), g) === 'effect'; }
    function isGenerator(g) { g = D(g); const k = kk(g); if (GENERATOR_BI.has(k)) return true; return (userPreds.has(k) || srcPreds.has(k)) && info.has(k) && !info.get(k).writes; }

    function genConj(gs, L, O, ctx) {
      gs = gs.filter(g => !(D(g).t === 'a' && D(g).n === 'true'));
      if (!gs.length) return genGoal(P.TRUE, L, O, ctx);
      if (gs.length === 1) return genGoal(gs[0], L, O, ctx);
      // MNN: fuse a prefix of deterministic builtins (rule det_prefix)
      if (feat.fuse && isDetBi(gs[0])) {
        let i = 0; while (i < gs.length && isDetBi(gs[i])) i++;
        const pre = gs.slice(0, i), rest = gs.slice(i);
        step('det_prefix', ctx.k, show(conj(pre)), { n: pre.length });
        if (!rest.length) return [Cmp('if_commit', [conj(pre), eq(O, list([E(L)])), eq(O, NIL)])];
        return [Cmp('if_commit', [conj(pre), conj(genConj(rest, L, O, ctx)), eq(O, NIL)])];
      }
      // MNN: an effect followed by the rest (rule effect_prefix)
      if (feat.fuse && isEffect(gs[0])) {
        const T = fresh(ctx, 'T'), O1 = fresh(ctx, 'R');
        step('effect_prefix', ctx.k, show(gs[0]));
        return [Cmp('effect_text', [gs[0], T])].concat(genConj(gs.slice(1), L, O1, ctx), [eq(O, cons(Cmp('out', [T]), O1))]);
      }
      // MNN: splice independent generators (rule splice)
      if (feat.splice && gs.length >= 2 && isGenerator(gs[0]) && isGenerator(gs[1])) {
        const v0 = new Set(termVars(gs[0])); const shared = termVars(gs[1]).some(v => v0.has(v));
        if (!shared) {
          const st = step('splice', ctx.k, show(conj([gs[0], gs[1]])), { gens: [show(gs[0]), show(gs[1])] });
          const PA = fresh(ctx, 'P'), PB = fresh(ctx, 'P'), O1 = fresh(ctx, 'R');
          const pat = g => { g = D(g); return list(g.t === 'c' ? g.a : []); };
          const packet = (g, Pv) => { g = D(g); const k = kk(g); if (GENERATOR_BI.has(k)) return Cmp('builtin_rows', [g, Pv]); return Cmp(cpName(P.name(g)), (g.t === 'c' ? g.a : []).concat([Pv])); };
          const patB = g => { g = D(g); return GENERATOR_BI.has(kk(g)) ? list([g]) : pat(g); };
          const chain = [packet(gs[0], PA), Cmp('if_commit', [eq(PA, NIL), eq(O1, NIL), conj([packet(gs[1], PB), Cmp('splice2', [PA, PB, patB(gs[0]), patB(gs[1]), E(L), O1])])])];
          // sequential fallback, generated without splicing
          const save = feat.splice; feat.splice = false;
          const seq = genConj([gs[0], gs[1]], L, O1, ctx);
          feat.splice = save;
          const code = [Cmp('if_commit', [Cmp('splice_safe', [patB(gs[0]), patB(gs[1])]), conj(chain), conj(seq)])];
          if (gs.length === 2) { code.push(eq(O, O1)); return code; }
          return code.concat(genRows(O1, gs.slice(2), L, O, ctx));
        }
      }
      const R1 = fresh(ctx, 'R');
      const first = genGoal(gs[0], L, R1, ctx);
      return first.concat(genRows(R1, gs.slice(1), L, O, ctx));
    }
    // ROWS: map packet Rin through goals gs (each row is a copy of env L)
    function genRows(Rin, gs, L, O, ctx) {
      const nm = auxName(ctx, 's');
      const st = step('seq', ctx.k, show(conj(gs)), { aux: nm });
      const I = Var('I__1'), Is = Var('I__2'), O1 = Var('O__1'), O2 = Var('O__2'), Oo = Var('O__0'), T = Var('T__0'), Row = Var('W__0');
      const m = new Map(); const L2 = copy(L, m); // same names
      const Ob = Var('O__0');
      const code = genConj(gs.map(g => copy(g, m)), L2, Ob, ctx);
      // the four clauses are added together so the predicate stays contiguous
      const mine = [Cmp(nm, [NIL, NIL]),
        ctx.marks
          ? Cmp(':-', [Cmp(nm, [cons(I, Is), Oo]), conj([Cmp(nm + 'r', [I, O1]), Cmp('if_commit', [Cmp('cut_in', [I, O1]), eq(Oo, O1), conj([Cmp(nm, [Is, O2]), Cmp('rows_concat', [list([O1, O2]), Oo])])])])])
          : Cmp(':-', [Cmp(nm, [cons(I, Is), Oo]), conj([Cmp(nm + 'r', [I, O1]), Cmp(nm, [Is, O2]), Cmp('rows_concat', [list([O1, O2]), Oo])])]),
        Cmp(nm + 'r', [Cmp('out', [T]), list([Cmp('out', [T])])]),
        Cmp(':-', [Cmp(nm + 'r', [E(Row), Ob]), conj([Cmp('copy_term', [Row, L2])].concat(code))])];
      if (ctx.marks) mine.push(Cmp(nm + 'r', [Atom('cut'), list([Atom('cut')])]));
      insertAux(ctx, st, mine);
      return [Cmp(nm, [Rin, O])];
    }
    function genDisj(alts, L, O, ctx, g) {
      const st = step('disj', ctx.k, show(g), { n: alts.length });
      const code = []; const Rs = [];
      alts.forEach((a, i) => {
        const nm = auxName(ctx, 'd');
        const Ei = fresh(ctx, 'E'), Ri = fresh(ctx, 'R');
        code.push(Cmp('copy_term', [E(L), Ei]), Cmp(nm, [Ei, Ri])); Rs.push(Ri);
        const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0');
        const body = genGoal(copy(a, m), L2, Ob, ctx);
        addAux(ctx, st, Cmp(':-', [Cmp(nm, [E(L2), Ob]), conj(body)]));
      });
      code.push(Cmp(ctx.marks ? 'rows_concat_cut' : 'rows_concat', [list(Rs), O]));
      return code;
    }
    function genIte(C, T, F, L, O, ctx, g, kind) {
      if (feat.fuse && flatConj(C).every(isDetBi)) {
        step(kind === 'neg' ? 'neg_det' : 'ite_det', ctx.k, show(g));
        return [Cmp('if_commit', [C, conj(genGoal(T, L, O, ctx)), conj(genGoal(F, L, O, ctx))])];
      }
      const sc = feat.scan && scanShape(C);
      if (sc) return genScan(sc, T, F, L, O, ctx, g, kind);
      const st = step(kind === 'neg' ? 'neg' : 'ite', ctx.k, show(g));
      const nmC = auxName(ctx, 'k'), nm = auxName(ctx, 'i');
      const EC = fresh(ctx, 'E'), RC = fresh(ctx, 'R'), Pre = fresh(ctx, 'R'), First = fresh(ctx, 'P'), RB = fresh(ctx, 'R');
      const mine = [];
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); mine.push(Cmp(':-', [Cmp(nmC, [E(L2), Ob]), conj(genGoal(copy(C, m), L2, Ob, ctx))])); }
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); mine.push(Cmp(':-', [Cmp(nm, [NIL, E(L2), Ob]), conj(genGoal(copy(F, m), L2, Ob, ctx))])); }
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); mine.push(Cmp(':-', [Cmp(nm, [cons(E(L2), Var('_')), Var('_'), Ob]), conj(genGoal(copy(T, m), L2, Ob, ctx))])); }
      insertAux(ctx, st, mine);
      return [Cmp('copy_term', [E(L), EC]), Cmp(nmC, [EC, RC]), Cmp('packet_first', [RC, Pre, First]), Cmp(nm, [First, E(L), RB]), Cmp('rows_concat', [list([Pre, RB]), O])];
    }
    // (Pre, member(X, Xs), Post) with Pre and Post deterministic builtins: the condition's first answer is
    // the first element of Xs that passes Post.  Nothing after that element is tried, as in Prolog.
    function scanShape(C) {
      const gs = flatConj(C).filter(x => !(D(x).t === 'a' && D(x).n === 'true'));
      const i = gs.findIndex(x => !isDetBi(x));
      if (i < 0) return null;
      const gen = D(gs[i]); const gk = kk(gen);
      const post = gs.slice(i + 1);
      if (!post.every(isDetBi)) return null;
      if (gk === 'member/2' && !userPreds.has('member/2') && !srcPreds.has('member/2')) return { pre: gs.slice(0, i), gen, post };
      // a predicate of facts (no cut, not dynamic): its first answer is the first fact that unifies
      const inf = info.get(gk);
      if (inf && inf.facts && !inf.dyn && !inf.cut && !queryPreds.has(gk) && feat.factScan) return { pre: gs.slice(0, i), gen, post, facts: gk };
      return null;
    }
    // nm(Xs, e(L), O) :- if_commit(Xs = [Y|Ys], if_commit((X = Y, Post), T(L, O), nm(Ys, e(L), O)), F(L, O)).
    // The condition binds the environment in place: if_commit/3 undoes a failed attempt, and the first success
    // is the row T runs on.  An open list is extended one cell at a time, as member/2 does.
    function genScan(sc, T, F, L, O, ctx, g, kind) {
      const st = step(kind === 'neg' ? 'neg_scan' : 'ite_scan', ctx.k, show(g), { gen: show(sc.gen), filters: sc.pre.concat(sc.post).map(x => show(x)), facts: sc.facts || null });
      const nm = auxName(ctx, 'q');
      const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0');
      const Xs = Var('Y__1'), Y = Var('Y__2'), Ys = Var('Y__3');
      const gen2 = copy(sc.gen, m);
      // member/2: X = Y.  facts: the fact (renamed apart) unifies with the call's arguments
      const first = sc.facts ? Cmp('copy_term', [Y, list(gen2.t === 'c' ? gen2.a : [])]) : eq(gen2.a[0], Y);
      const cond = conj([first].concat(sc.post.map(x => copy(x, m))));
      const tC = conj(genGoal(copy(T, m), L2, Ob, ctx)), fC = conj(genGoal(copy(F, m), L2, Ob, ctx));
      const body = Cmp('if_commit', [eq(Xs, cons(Y, Ys)), Cmp('if_commit', [cond, tC, Cmp(nm, [Ys, E(L2), Ob])]), fC]);
      insertAux(ctx, st, [Cmp(':-', [Cmp(nm, [Xs, E(L2), Ob]), body])]);
      let call = [Cmp(nm, [sc.gen.a[1], E(L), O])];
      if (sc.facts) { const Tb = fresh(ctx, 'F'); factRowsUsed.add(sc.facts); call = [Cmp(P.name(sc.gen) + '__rows', [Tb]), Cmp(nm, [Tb, E(L), O])]; }
      if (!sc.pre.length) return call;
      return [Cmp('if_commit', [conj(sc.pre), conj(call), conj(genGoal(F, L, O, ctx))])];
    }
    function genFindall(g, L, O, ctx, agg) {
      const st = step(agg ? 'aggregate' : 'findall', ctx.k, show(agg || g), {});
      const Tm = g.a[0], G = g.a[1], Res = g.a[2];
      const nm = auxName(ctx, 'f');
      const EG = fresh(ctx, 'E'), TG = fresh(ctx, 'T'), RG = fresh(ctx, 'R'), Outs = fresh(ctx, 'R'), Rw = fresh(ctx, 'R'), Ts = fresh(ctx, 'T');
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); addAux(ctx, st, Cmp(':-', [Cmp(nm, [E(L2), Ob]), conj(genGoal(copy(G, m), L2, Ob, ctx))])); }
      const code = [Cmp('copy_term', [Cmp('f', [E(L), Tm]), Cmp('f', [EG, TG])]), Cmp(nm, [EG, RG]), Cmp('packet_split', [RG, Outs, Rw]), Cmp('project_list', [Rw, EG, TG, Ts])];
      let result = Ts;
      if (agg) { const R2 = fresh(ctx, 'T'); code.push(Cmp('aggregate_list', [D(agg.a[0]).t === 'c' ? Atom(D(agg.a[0]).f) : D(agg.a[0]), Ts, R2])); result = R2; Res2(agg.a[2]); }
      function Res2() { }
      const target = agg ? agg.a[2] : Res;
      if (agg) {
        // aggregate_list fails for max/min of an empty list: then the goal has no answer
        const last = code.pop();
        code.push(Cmp('if_commit', [conj([last, eq(target, result)]), Cmp('rows_concat', [list([Outs, list([E(L)])]), O]), eq(O, Outs)]));
      } else {
        code.push(Cmp('if_commit', [eq(target, result), Cmp('rows_concat', [list([Outs, list([E(L)])]), O]), eq(O, Outs)]));
      }
      return code;
    }

    // fact tables for scans:  p__rows([[Args1], [Args2], ...]).
    for (const k of factRowsUsed) {
      const [f] = splitKey(k);
      const rows = srcPreds.get(k).filter(Boolean).map(c => list(D(c.head).t === 'c' ? D(c.head).a : []));
      const st = step('FACTS', k, srcPreds.get(k).filter(Boolean).map(c => c.origText).join('\n'), { n: rows.length, table: true });
      const at = out.clauses.findIndex(c => c.pred === k);
      const cl = { term: P.copy(Cmp(f + '__rows', [list(rows)])), step: st.id, pred: k };
      // keep the table with its predicate's other clauses
      let j = at; while (j >= 0 && j < out.clauses.length && out.clauses[j].pred === k) j++;
      if (at < 0) out.clauses.push(cl); else out.clauses.splice(j, 0, cl);
    }
    // inserting shifts clause positions: every step's clause list is rebuilt from the clauses
    if (factRowsUsed.size) { for (const st of out.steps) st.clauses = []; out.clauses.forEach((c, i) => out.steps[c.step - 1].clauses.push(i)); }

    // ---- 3. assemble ----
    out.genPreds = genPreds;
    out.srcPreds = srcPreds; out.order = order; out.prog = prog;
    // group clauses by generated predicate in order
    out.text = printDetlog(out);
    return out;
  }

  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }
  function sccs(nodes, succ) {
    let index = 0; const st = []; const idx = new Map(), low = new Map(), on = new Set(); const res = new Map();
    function sc(v) {
      idx.set(v, index); low.set(v, index); index++; st.push(v); on.add(v);
      for (const w of succ(v)) { if (!idx.has(w)) { sc(w); low.set(v, Math.min(low.get(v), low.get(w))); } else if (on.has(w)) low.set(v, Math.min(low.get(v), idx.get(w))); }
      if (low.get(v) === idx.get(v)) { const comp = new Set(); let w; do { w = st.pop(); on.delete(w); comp.add(w); } while (w !== v); for (const x of comp) res.set(x, comp); }
    }
    for (const v of nodes) if (!idx.has(v)) sc(v);
    return res;
  }

  // ----- S2A: answer table of a pure predicate's most general goal -----
  function s2aTable(prog, f, n, max) {
    const A = []; for (let i = 0; i < n; i++) A.push(Var());
    const g = Cmp(f, A);
    const eng = new P.Engine(prog, { stepLimit: 200000 });
    const rows = [];
    try {
      let tooMany = false;
      eng.solve(g, () => { if (rows.length >= max) { tooMany = true; return false; } rows.push(A.map(a => P.resolve(a))); return true; });
      if (tooMany) return { ok: false, why: 'more than ' + max + ' answers' };
    } catch (e) { return { ok: false, why: e.limit ? 'its table is not finite within the step limit' : 'its most general goal raises ' + (e.term ? P.errText(e.term) : e.message) }; }
    if (eng.out.length) return { ok: false, why: 'writes output' };
    if (!rows.length) return { ok: false, why: 'no answers' };
    if (!rows.every(r => r.every(P.isGround))) return { ok: false, why: 'answers are not ground' };
    return { ok: true, rows };
  }
  function s2aSpec(rows, n) {
    const K = rows.length; const cols = [];
    for (let j = 0; j < n; j++) {
      const vals = rows.map(r => D(r[j]));
      if (vals.every(v => P.compare(v, vals[0]) === 0)) { cols.push(Cmp('const', [vals[0]])); continue; }
      if (vals.every(v => v.t === 'n' && !v.f)) {
        const nw = newtonFit(vals.map(v => v.v));
        if (nw) { cols.push(Cmp('newton', [list(nw.map(Int))])); continue; }
      }
      cols.push(Cmp('data', [list(vals)]));
    }
    return Cmp('s2a', [Int(K), list(cols)]);
  }
  function newtonFit(ys) {
    const K = ys.length; const ds = []; let cur = ys.slice();
    for (let d = 0; d <= 3; d++) {
      ds.push(cur[0]);
      const next = []; for (let i = 0; i + 1 < cur.length; i++) next.push(cur[i + 1] - cur[i]);
      if (next.every(x => x === 0)) { return K >= d + 2 ? ds : null; }
      cur = next; if (!cur.length) return null;
    }
    return null;
  }
  // Newton form D0 + D1*C(I,1) + D2*C(I,2) + D3*C(I,3)  ->  integer polynomial (c0 + c1*I + c2*I^2 + c3*I^3) / den
  function newtonPoly(ds) {
    const c = [0, 0, 0, 0];
    const d = i => ds[i] || 0;
    c[0] += 6 * d(0); c[1] += 6 * d(1);
    c[1] += -3 * d(2); c[2] += 3 * d(2);
    c[1] += 2 * d(3); c[2] += -3 * d(3); c[3] += d(3);
    const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a; };
    let g = 6; for (const x of c) g = gcd(g, x);
    return { c: c.map(x => x / g), den: 6 / g };
  }
  function polyText(ds, I) {
    const { c, den } = newtonPoly(ds); const mon = ['', I, I + '*' + I, I + '*' + I + '*' + I];
    const parts = [];
    for (let k = 3; k >= 0; k--) { if (!c[k]) continue; const a = Math.abs(c[k]); const t = k === 0 ? String(a) : (a === 1 ? mon[k] : a + '*' + mon[k]); parts.push((c[k] < 0 ? '-' : '+') + t); }
    let s = parts.join(' ').replace(/^\+/, '').replace(/ ([+-])/g, ' $1 ') || '0';
    s = s.replace(/^-/, '-');
    return den === 1 ? s : '(' + s + ')//' + den;
  }
  function s2aFormula(spec) {
    const cols = listToArray(D(spec).a[1]);
    return cols.map((c, j) => {
      c = D(c); const nm = 'A' + (j + 1);
      if (c.f === 'const') return nm + ' = ' + show(c.a[0]);
      if (c.f === 'data') return nm + ' = data[I]';
      return nm + ' = ' + polyText(listToArray(c.a[0]).map(x => D(x).v), 'I');
    }).join(', ');
  }
  P.newtonPoly = newtonPoly; P.polyText = polyText;
  P.s2aTable = s2aTable; P.s2aSpec = s2aSpec; P.newtonFit = newtonFit; P.s2aFormula = s2aFormula;

  // ----- printing -----
  function printDetlog(out) {
    const lines = [];
    lines.push('% Detlog generated by pl2detlog (' + (out.mode === 'mnn' ? 'MNN-optimised' : 'plain') + ').');
    lines.push('% No cut, ;, ->, \\+, findall, call/N or nondeterministic builtin: every predicate p/n');
    lines.push('% becomes p__cp/n+1, which succeeds once with its answer packet of e(Row) / out(Text) items.');
    if (out.report.length) lines.push(...out.report.map(r => '% ' + r));
    for (const gp of out.genPreds) for (const n of gp.notes) if (!n.startsWith('unfolded')) lines.push('% ' + gp.key + ': ' + n);
    lines.push('');
    let last = null;
    for (const cl of out.clauses) {
      if (cl.pred !== last) { if (last !== null) lines.push(''); lines.push('% ---- ' + cl.pred + ' ----'); last = cl.pred; }
      lines.push(P.showClause(cl.term, { varName: v => v.name || ('_G' + v.id) }));
    }
    return lines.join('\n') + '\n';
  }
  P.printDetlog = printDetlog;
  P.convert = convert;
  P.flatConj = flatConj; P.conjT = conj;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog Detlog engine: runs converted Detlog without choicepoints.
   Every call commits to the single clause its first argument selects; if_commit/3 is the only decision
   construct (the head of its condition, else branch only when the condition has no answer).
   Calls where more than one clause matches are counted as determinism violations. */
(function (P) {
  'use strict';
  const { Atom, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, isNil, listToArray, copy, termVars, isGround, compare, show, variantKey } = P;
  const D = deref;

  function DetEngine(prog, opts) {
    opts = opts || {};
    this.prog = prog; this.trail = []; this.steps = 0; this.decisions = 0; this.violations = []; this.maxDecisionDepth = 0;
    this.out = ''; this.stepLimit = opts.stepLimit || 2e7; this.memo = new Map(); this.memoHits = 0; this.memoStores = 0;
    this.globals = new Map(); this.rowsBuilt = 0; this.maxRows = 0;
    this.depth = 0;
    // clauses by predicate key (the program's own map: nothing to build per run)
    this.index = prog.preds;
  }
  DetEngine.prototype.bind = function (v, t) { v.ref = t; this.trail.push(v); };
  DetEngine.prototype.undo = function (mark) { const tr = this.trail; while (tr.length > mark) tr.pop().ref = null; };
  DetEngine.prototype.mark = function () { return this.trail.length; }; // every binding is trailed here
  DetEngine.prototype.unify = P.Engine.prototype.unify;
  DetEngine.prototype.write = function (s) { this.out += s; };
  DetEngine.prototype.tick = function (n) { this.steps += n || 1; if (this.steps > this.stepLimit) throw new P.LimitError('step limit (' + this.stepLimit + ') exceeded'); };

  DetEngine.prototype.solve = function (goal) {
    const self = this;
    let goals = { g: goal, next: null };
    const marks = [];
    const fail = () => {
      if (!marks.length) return false;
      const m = marks.pop(); self.undo(m.trail); goals = m.els; return true;
    };
    for (;;) {
      if (goals === null) return true;
      const fr = goals; goals = fr.next;
      const g = D(fr.g);
      self.tick();
      let f, a;
      if (g.t === 'a') { f = g.n; a = []; } else if (g.t === 'c') { f = g.f; a = g.a; } else throw P.typeError('callable', g);
      const k = f + '/' + a.length;
      switch (k) {
        case 'true/0': continue;
        case 'fail/0': case 'false/0': if (!fail()) return false; continue;
        case ',/2': self.steps--; goals = { g: a[0], next: { g: a[1], next: goals } }; continue;
        case 'if_commit/3': {
          self.decisions++;
          const mk = { trail: self.trail.length, els: { g: a[2], next: goals } };
          marks.push(mk); if (marks.length > self.maxDecisionDepth) self.maxDecisionDepth = marks.length;
          goals = { g: a[0], next: { g: Cmp('$commit', [{ t: 'n', v: 0, mk }]), next: { g: a[1], next: goals } } };
          continue;
        }
        case '$commit/1': { const mk = a[0].mk; const i = marks.lastIndexOf(mk); if (i >= 0) marks.splice(i, 1); self.steps--; continue; }
        case ';/2': case '->/2': case '\\+/1': case '!/0': case 'findall/3': case 'call/1':
          throw new Error('Detlog engine: ' + k + ' is not Detlog (the converted program must not contain it)');
      }
      const cls = self.index.get(k);
      if (cls) {
        // first-argument selection
        let chosen = -1; const m0 = self.trail.length; let body = null;
        // first-argument indexing, as SWI-Prolog does it: more than one compatible clause = a choicepoint
        const cand = [];
        for (let i = 0; i < cls.length; i++) if (!a.length || P.firstArgMayMatch(a[0], cls[i].head.a[0])) cand.push(i);
        if (cand.length > 1 && self.violations.length < 1000) self.violations.push(k);
        for (const i of cand) {
          const cl = cls[i];
          const mp = new Map(); const h = copy(cl.head, mp);
          if (self.unify(h, g)) { chosen = i; body = copy(cl.body, mp); break; }
          self.undo(m0);
        }
        if (chosen < 0) { if (!fail()) return false; continue; }
        const bd = D(body);
        if (!(bd.t === 'a' && bd.n === 'true')) goals = { g: body, next: goals };
        continue;
      }
      const rb = RUNTIME[k] || (P.builtins[k] && !P.builtins[k].nondet && !P.builtins[k].call ? P.builtins[k].fn : null);
      if (rb) {
        const mark = self.trail.length;
        if (!rb(a, self, g)) { self.undo(mark); if (!fail()) return false; }
        continue;
      }
      if (P.builtins[k]) throw new Error('Detlog engine: nondeterministic builtin ' + k + ' called directly (it must be wrapped in builtin_rows/2)');
      throw new Error('Detlog engine: unknown procedure ' + k);
    }
  };
  // would clause head `head` match goal g as the call was (before bindings made after mark m0)?
  DetEngine.prototype.unifyProbe = function (head, g, m0) {
    // snapshot the bindings made since m0, undo them, test, then redo
    const made = this.trail.slice(m0).map(v => [v, v.ref]);
    for (let i = made.length - 1; i >= 0; i--) made[i][0].ref = null;
    const save = this.trail.length; this.trail.length = m0;
    const mk = this.trail.length;
    const ok = this.unify(copy(head), g);
    this.undo(mk);
    for (const [v, r] of made) v.ref = r;
    this.trail.length = m0; for (const [v] of made) this.trail.push(v);
    return ok;
  };

  // ---------------- runtime (deterministic, no choicepoints) ----------------
  const RUNTIME = {};
  const R = (k, fn) => { RUNTIME[k] = fn; };
  const items = t => { const a = listToArray(t); if (!a) throw new Error('packet is not a proper list: ' + show(t)); return a; };
  const isOut = t => { t = D(t); return t.t === 'c' && t.f === 'out' && t.a.length === 1; };
  const isRow = t => { t = D(t); return t.t === 'c' && t.f === 'e' && t.a.length === 1; };
  const isCut = t => { t = D(t); return t.t === 'a' && t.n === 'cut'; };
  // cut markers: a cut reached on a row emits [cut, e(Row)]; loops stop after it, concatenations drop what follows
  const hasCut = xs => xs.some(isCut);
  R('rows_concat_cut/2', (a, e) => { const ls = items(a[0]); let all = []; for (const l of ls) { const x = items(l); e.tick(x.length); all = all.concat(x); if (hasCut(x)) break; } return e.unify(a[1], list(all)); });
  R('rows_cut_concat/2', (a, e) => { const ls = items(a[0]); let all = []; for (const l of ls) { const x = items(l); e.tick(x.length); all = all.concat(x.filter(y => !isCut(y))); if (hasCut(x)) break; } return e.unify(a[1], list(all)); });
  R('strip_cut/2', (a, e) => { const x = items(a[0]); e.tick(x.length); return e.unify(a[1], list(x.filter(y => !isCut(y)))); });
  R('cut_in/2', (a, e) => { if (!isRow(a[0])) return false; const x = items(a[1]); e.tick(); return hasCut(x); });
  R('rows_concat/2', (a, e) => {
    // like append/3: every list but the last is copied, the last is shared
    const ls = items(a[0]); if (!ls.length) return e.unify(a[1], NIL);
    const all = []; for (let i = 0; i < ls.length - 1; i++) { const x = items(ls[i]); e.tick(x.length); for (const y of x) all.push(y); }
    e.rowsBuilt += all.length;
    return e.unify(a[1], list(all, ls[ls.length - 1]));
  });
  // Rows are renamed apart by copying.  When the instantiated result is ground there is nothing to rename:
  // unify in place, resolve, undo.  NO = the unification failed; null = not ground (copy as before).
  const NO = {};
  const isG = r => r.t !== 'v' && (r.t !== 'c' || r.gr === true);
  // One pass: unify the pattern with the row in place, copy the instantiated output (copy dereferences bindings
  // and renames what is still unbound, so the result shares no variable with the environment), undo.
  // A variable private to the row is renamed too, which no answer can observe.
  function groundRow(e, pat, val, out) {
    const mk = e.trail.length; let r = NO;
    if (e.unify(pat, val)) r = copy(out);
    e.undo(mk); return r;
  }
  // splice_extend(Packet, Pattern, e(Env), Out)
  R('splice_extend/4', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const x = D(it);
      if (isOut(x) || isCut(x)) { res.push(x); continue; }
      const g = groundRow(e, a[1], x.a[0], a[2]);
      if (g === NO) continue;
      if (g !== null) { res.push(g); continue; }
      const c = copy(Cmp('-', [a[1], a[2]]));
      const mk = e.trail.length;
      if (e.unify(c.a[0], x.a[0])) res.push(P.resolve(c.a[1]));
      e.undo(mk);
    }
    e.rowsBuilt += res.length; if (res.length > e.maxRows) e.maxRows = res.length;
    return e.unify(a[3], list(res));
  });
  // project_rows(EnvPacket, EnvVars, HeadArgs, Rows)
  R('project_rows/4', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const x = D(it);
      if (isOut(x) || isCut(x)) { res.push(x); continue; }
      const g = groundRow(e, a[1], x.a[0], a[2]);
      if (g === NO) continue;
      if (g !== null) { res.push(Cmp('e', [g])); continue; }
      const c = copy(Cmp('-', [a[1], a[2]]));
      const mk = e.trail.length;
      if (e.unify(c.a[0], x.a[0])) res.push(Cmp('e', [P.resolve(c.a[1])]));
      e.undo(mk);
    }
    return e.unify(a[3], list(res));
  });
  // project_list(Rows, e(EnvPattern), Template, Values)
  R('project_list/4', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const x = D(it); if (!isRow(x)) continue;
      const g = groundRow(e, a[1], x, a[2]);
      if (g === NO) continue;
      if (g !== null) { res.push(g); continue; }
      const c = copy(Cmp('-', [a[1], a[2]]));
      const mk = e.trail.length;
      if (e.unify(c.a[0], x)) res.push(P.resolve(c.a[1]));
      e.undo(mk);
    }
    return e.unify(a[3], list(res));
  });
  R('packet_first/3', (a, e) => {
    const xs = items(a[0]); const pre = [];
    for (const x of xs) { e.tick(); if (isCut(x)) continue; if (isOut(x)) { pre.push(D(x)); continue; } return e.unify(a[1], list(pre)) && e.unify(a[2], list([x])); }
    return e.unify(a[1], list(pre)) && e.unify(a[2], NIL);
  });
  R('packet_split/3', (a, e) => { const outs = [], rows = []; for (const x of items(a[0])) { e.tick(); if (isCut(x)) continue; (isOut(x) ? outs : rows).push(D(x)); } return e.unify(a[1], list(outs)) && e.unify(a[2], list(rows)); });
  R('effect_text/2', (a, e) => {
    const g = D(a[0]); const k = P.key(g); const bi = P.builtins[k];
    if (!bi) throw new Error('effect_text: unknown output builtin ' + k);
    const saveOut = e.out; e.out = '';
    try { bi.fn(g.t === 'c' ? g.a : [], e, g); } finally { var txt = e.out; e.out = saveOut; }
    return e.unify(a[1], Str(txt));
  });
  R('builtin_rows/2', (a, e) => {
    const g = D(a[0]); const k = P.key(g); const bi = P.builtins[k];
    if (!bi || !bi.nondet) throw new Error('builtin_rows: ' + k + ' is not a nondeterministic builtin');
    const res = []; const mk = e.trail.length;
    const it = bi.fn(g.t === 'c' ? g.a : [], e, g);
    let guard = 0;
    for (;;) {
      const r = it.next(); if (r.done) break;
      e.tick(); res.push(Cmp('e', [list([copy(g)])]));
      if (++guard > 1e6 || res.length > 1e6) throw new P.LimitError('builtin_rows: infinite generator ' + k + ' (no finite packet)');
      if (e.steps > e.stepLimit) throw new P.LimitError('step limit exceeded');
    }
    e.undo(mk);
    return e.unify(a[1], list(res));
  });
  R('cp_filter/3', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const c = copy(a[1]); const f = copy(D(it).a[0]);
      const mk = e.trail.length;
      if (e.unify(c, f)) res.push(Cmp('e', [P.resolve(c)]));
      e.undo(mk);
    }
    return e.unify(a[2], list(res));
  });
  R('aggregate_list/3', (a, e) => {
    const sp = D(a[0]).n; const ts = items(a[1]); e.tick(ts.length);
    let r;
    switch (sp) {
      case 'count': r = Int(ts.length); break;
      case 'sum': { let s = Int(0); for (const x of ts) s = P.evalArith(Cmp('+', [s, x])); r = s; break; }
      case 'max': if (!ts.length) return false; r = ts.map(P.evalArith).reduce((m, x) => x.v > m.v ? x : m); break;
      case 'min': if (!ts.length) return false; r = ts.map(P.evalArith).reduce((m, x) => x.v < m.v ? x : m); break;
      case 'bag': r = list(ts); break;
      case 'set': r = list(P.sortUnique(ts)); break;
      default: throw new Error('aggregate_list: unknown spec ' + sp);
    }
    return e.unify(a[2], r);
  });
  R('splice_safe/2', (a) => { const va = new Set(termVars(a[0])); return !termVars(a[1]).some(v => va.has(v)); });
  R('splice2/6', (a, e) => {
    const PA = items(a[0]), PB = items(a[1]); const res = [];
    for (const ra of PA) {
      if (isOut(ra)) { res.push(D(ra)); continue; }
      for (const rb of PB) {
        e.tick();
        if (isOut(rb)) continue;
        const c = copy(Cmp('f', [a[2], a[3], a[4]]));
        const mk = e.trail.length;
        if (e.unify(c.a[0], D(ra).a[0]) && e.unify(c.a[1], D(rb).a[0])) res.push(P.resolve(c.a[2]));
        e.undo(mk);
      }
    }
    e.rowsBuilt += res.length;
    return e.unify(a[5], list(res));
  });
  R('memo_lookup/3', (a, e) => {
    const key = variantKey(Cmp('k', [a[0], a[1]]));
    const hit = e.memo.get(key);
    if (hit) { e.memoHits++; e.tick(); return e.unify(a[2], Cmp('found', [renameRows(hit, a[1])])); }
    return e.unify(a[2], Atom('none'));
  });
  // rows were stored relative to a variant of the call; rebuild them for this call's variables
  function renameRows(stored, callArgs) {
    const c = copy(stored); // c = f(StoredArgs, Rows)
    const mk = [];
    // map stored call variables onto this call's variables (variant => bijection)
    const sv = termVars(c.a[0]), cv = termVars(callArgs);
    sv.forEach((v, i) => { v.ref = cv[i]; mk.push(v); });
    const r = P.resolve(c.a[1]);
    for (const v of mk) v.ref = null;
    return r;
  }
  R('memo_store/3', (a, e) => {
    const key = variantKey(Cmp('k', [a[0], a[1]]));
    if (!e.memo.has(key)) { e.memo.set(key, copy(Cmp('f', [a[1], a[2]]))); e.memoStores++; }
    return true;
  });
  // s2a_rows(s2a(K, Cols), Args, Rows)
  // the specification is a constant of the program: it is decoded once (per specification term), and its
  // table of values is built once, so a call costs one unification per candidate row
  const s2aCache = new WeakMap();
  function s2aDecode(spec) {
    let d = s2aCache.get(spec); if (d) return d;
    const K = D(spec.a[0]).v; const cols = items(spec.a[1]).map(D);
    const dec = cols.map(c => c.f === 'const' ? { k: 'const', v: c.a[0] } : c.f === 'data' ? { k: 'data', vs: items(c.a[0]) } : { k: 'newton', ds: items(c.a[0]).map(x => D(x).v) });
    const val = (c, I) => { if (c.k === 'const') return c.v; if (c.k === 'data') return c.vs[I]; let s = 0; for (let j = 0; j < c.ds.length; j++) s += c.ds[j] * binom(I, j); return Int(s); };
    const rows = []; for (let I = 0; I < K; I++) { const r = list(dec.map(c => val(c, I))); markGr(r); rows.push(r); }
    d = { K, dec, rows }; s2aCache.set(spec, d); return d;
  }
  function markGr(t) { t = D(t); if (t.t === 'c') { if (P.isGround(t)) { (function m(x) { x = D(x); if (x.t === 'c' && !x.gr) { x.gr = true; x.a.forEach(m); } })(t); } } }
  R('s2a_rows/3', (a, e) => {
    const spec = D(a[0]); const { K, dec, rows } = s2aDecode(spec); const args = items(a[1]);
    // direct solve on a bound linear column
    let only = null;
    for (let j = 0; j < dec.length; j++) {
      const c = dec[j], x = D(args[j]);
      if (c.k === 'newton' && x.t === 'n' && !x.f) {
        const ds = c.ds;
        if (ds.length === 2 && ds[1] !== 0) { const q = typeof x.v === 'number' ? (x.v - ds[0]) / ds[1] : NaN; only = Number.isInteger(q) && q >= 0 && q < K ? [q] : []; break; }
      }
    }
    const res = []; const al = a[1]; const n = only ? only.length : K;
    for (let i = 0; i < n; i++) {
      const I = only ? only[i] : i;
      e.tick();
      // one pass: unify the arguments with the row in place, copy them (renaming what stays unbound), undo
      const mk = e.trail.length;
      if (e.unify(al, rows[I])) res.push(Cmp('e', [copy(al)]));
      e.undo(mk);
    }
    return e.unify(a[2], list(res));
  });
  function binom(n, k) { let r = 1; for (let i = 0; i < k; i++) r = r * (n - i) / (i + 1); return Math.round(r); }
  R('detlog_unsupported/2', (a) => { throw new Error('not converted: ' + show(a[0]) + ': ' + P.textOf(a[1])); });
  P.binom = binom;
  P.DETLOG_RUNTIME = RUNTIME;

  // run a converted query predicate '$queryN'/k: returns events like runQuery
  function runDetlog(prog, qpred, varNames, opts) {
    opts = opts || {};
    const eng = new DetEngine(prog, opts);
    const vs = varNames.map(n => Var(n)); const Rv = Var('R');
    const goal = Cmp(qpred + '__cp', vs.concat([Rv]));
    const t0 = P.now(); let ok = false, error = null;
    try { ok = eng.solve(goal); } catch (e) { error = e.message; if (opts.debug) console.error(e); }
    const t1 = P.now();
    const dec = decodePacket(ok, error, Rv, varNames); const { answers, events, output } = dec; error = dec.error;
    return { ok: !error, answers, events, output, steps: eng.steps, decisions: eng.decisions, violations: eng.violations.length, violationPreds: [...new Set(eng.violations)], cps: 0, maxCP: 0, timeMs: t1 - t0, error, memoHits: eng.memoHits, memoStores: eng.memoStores, rowsBuilt: eng.rowsBuilt, maxRows: eng.maxRows };
  }
  function decodePacket(ok, error, Rv, varNames) {
    const events = [], answers = []; let output = '';
    if (ok) {
      for (const it of listToArray(Rv) || []) {
        const x = D(it);
        if (x.t === 'a') continue;
        if (x.f === 'out') { const txt = P.textOf(x.a[0]); output += txt; const last = events[events.length - 1]; if (last && last.k === 'out') last.text += txt; else events.push({ k: 'out', text: txt }); continue; }
        const row = listToArray(x.a[0]); const nm = P.namer();
        const text = varNames.length ? varNames.map((n, i) => n + ' = ' + show(row[i], { varName: nm })).join(', ') : 'true';
        answers.push({ text }); events.push({ k: 'row', text });
      }
    } else if (!error) error = 'Detlog query failed (a packet predicate must always succeed)';
    return { ok: !error, answers, events, output, error };
  }
  P.decodePacket = decodePacket;
  P.DetEngine = DetEngine; P.runDetlog = runDetlog;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

// native.js - the native tier's compiler, shared by the JavaScript JIT (detlog_fast.js) and the C export (cgen.js).
// A deterministic-mode predicate p__d(X1..Xn, S), entered with ground inputs ('i', or 'n' for an integer) and
// fresh, distinct output variables ('o'), is compiled for that mode to a function of its inputs that returns its
// outputs, or NO / MAYBE: ground terms in and out, no logic variables, no trail, integer arithmetic on raw
// integers, direct calls between native functions, tabled calls memoised.  The analysis is abstract
// interpretation over the Detlog of p__d: each variable is G (ground: a local holds it; int: it is a raw
// integer), F (fresh), P (pending: built from parts that become ground later) or U (unknown: give up).
// Anything the analysis cannot follow throws NOPE: no native function for that mode.  The emitter (EM) gives
// the target language; the analysis and the decisions are the same for every target.
(function (P) {
  'use strict';
  const D = P.deref, Cmp = P.Cmp;
  const termVars = P.termVars;
  const NOPE = { nope: true };
  function nope() { if (P.NATIVE_DEBUG) P.NATIVE_WHY = new Error().stack.split('\n')[2]; throw NOPE; }
  function sameTerm(a, b) { a = D(a); b = D(b); if (a === b) return true; if (a.t !== b.t) return false; if (a.t === 'c') return a.f === b.f && a.a.length === b.a.length && a.a.every((x, i) => sameTerm(x, b.a[i])); if (a.t === 'a') return a === b; if (a.t === 'n') return a.v === b.v && a.f === b.f; if (a.t === 's') return a.v === b.v; return false; }

  // one function: returns { src, intRet, params, outs } for EM to place, or throws NOPE
  function genNative(prog, k, mode, fnName, need, selfInt, EM) {
    const cls = prog.preds.get(k); if (!cls || cls.length !== 1) nope();
    const cl = P.copy(Cmp('-', [cls[0].head, cls[0].body]));
    const head = D(cl.a[0]); const n = head.a.length - 1;
    const S0 = D(head.a[n]); if (S0.t !== 'v') nope();
    const jsName = new Map(); let nv = 0, nl = 0;
    const js = v => { let x = jsName.get(v); if (!x) { x = 'v' + (nv++); jsName.set(v, x); } return x; };
    const used = new Map(); // local name|int -> {name, int}
    const V = x => { if (!x.param) used.set(x.js + '|' + !!x.int, { name: x.js, int: !!x.int }); return EM.v(x.js, !!x.int); };
    let st = new Map(); const params = [], outs = [];
    st.set(S0, { k: 'TOP' });
    for (let i = 0; i < n; i++) {
      const hv = D(head.a[i]); if (hv.t !== 'v' || st.has(hv)) nope();
      if (mode[i] === 'i') { st.set(hv, { k: 'G', js: 'a' + i, param: true }); params.push({ name: 'a' + i, int: false }); }
      else if (mode[i] === 'n') { st.set(hv, { k: 'G', js: 'a' + i, int: true, param: true }); params.push({ name: 'a' + i, int: true }); }
      else { st.set(hv, { k: 'F' }); outs.push(hv); }
    }
    const statusLocals = new Set();
    const get = (s, v) => s.get(v) || { k: 'F' };
    const clone = s => new Map(s);
    const join = (a, b) => {
      if (!a) return b; if (!b) return a;
      const r = new Map();
      for (const v of new Set([...a.keys(), ...b.keys()])) {
        const x = get(a, v), y = get(b, v);
        if (x.k === y.k && x.js === y.js && x.t === y.t && x.set === y.set && !!x.int === !!y.int) r.set(v, x); else r.set(v, { k: 'U' });
      }
      return r;
    };
    const ATOM = { yes: EM.YES, no: EM.NO, maybe: EM.MAYBE };
    const isStatusAtom = t => { t = D(t); return t.t === 'a' && ATOM[t.n] !== undefined; };
    const G_ = (s, v, int) => { s.set(v, { k: 'G', js: js(v), int: !!int }); return V(s.get(v)); };
    const allG = (t, s) => termVars(t).every(v => { const x = get(s, v); return x.k === 'G' || (x.k === 'P' && allG(x.t, s)); });
    const build = (t, s) => {
      t = D(t);
      if (t.t === 'v') { const x = get(s, t); if (x.k === 'G') return x.int ? EM.box(V(x)) : V(x); if (x.k === 'P') return build(x.t, s); nope(); }
      if (t.t !== 'c' || P.isGround(t)) return EM.k(t);
      return EM.cmp(t.f, t.a.map(x => build(x, s)));
    };
    let tmp = 0;
    // match a ground value (an expression) against a pattern: binds fresh variables, tests the rest
    function match(expr, pat, s, fail) {
      pat = D(pat);
      if (pat.t === 'v') {
        const x = get(s, pat);
        if (x.k === 'F') return EM.assign(G_(s, pat, false), expr);
        if (x.k === 'G') return 'if (!' + (x.int ? EM.isIntVal(expr, V(x)) : EM.eq(expr, V(x))) + ') ' + fail + '\n';
        if (x.k === 'P') return match(expr, x.t, s, fail);
        nope();
      }
      const t = 't' + (tmp++);
      if (pat.t !== 'c') return '{ ' + EM.tmp(t, expr) + ' if (!(' + EM.keyTest(pat, t) + ')) ' + fail + ' }\n';
      let code = '{ ' + EM.tmp(t, expr) + '\nif (!(' + EM.isCmp(t, pat.f, pat.a.length) + ')) ' + fail + '\n';
      pat.a.forEach((y, i) => { code += match(EM.arg(t, i), y, s, fail); });
      return code + '}\n';
    }
    // unification in functional mode; returns code, or null for a unification that fails statically
    function unify(a, b, s, fail) {
      a = D(a); b = D(b);
      if (a === b) return '';
      const xa = a.t === 'v' ? get(s, a) : null, xb = b.t === 'v' ? get(s, b) : null;
      if (xa && xa.k === 'U' || xb && xb.k === 'U') nope();
      if (xa && xa.k === 'F') {
        // an integer stays a raw integer: an integer constant, or another variable holding one
        if (b.t === 'n' && !b.f && Number.isSafeInteger(b.v)) return EM.assign(G_(s, a, true), EM.num(b.v));
        if (xb && xb.k === 'G' && xb.int) { const rhs = V(xb); return EM.assign(G_(s, a, true), rhs); }
        if (allG(b, s)) { const rhs = build(b, s); return EM.assign(G_(s, a, false), rhs); }
        if (termVars(b).includes(a)) nope(); s.set(a, { k: 'P', t: b }); return '';
      }
      if (xb && xb.k === 'F') return unify(b, a, s, fail);
      if (xa && xa.k === 'P') return unify(xa.t, b, s, fail);
      if (xb && xb.k === 'P') return unify(a, xb.t, s, fail);
      if (xa && xb) {
        if (xa.int && xb.int) return 'if (' + V(xa) + ' ' + EM.NEOP + ' ' + V(xb) + ') ' + fail + '\n';
        if (xa.int || xb.int) { const [i, t] = xa.int ? [xa, xb] : [xb, xa]; return 'if (!' + EM.isIntVal(V(t), V(i)) + ') ' + fail + '\n'; }
        return 'if (!' + EM.eq(V(xa), V(xb)) + ') ' + fail + '\n';
      }
      if (xa && xa.int) return intMatch(V(xa), b, fail);
      if (xb && xb.int) return intMatch(V(xb), a, fail);
      if (xa) return match(V(xa), b, s, fail);
      if (xb) return match(V(xb), a, s, fail);
      if (a.t !== b.t) return null;
      if (a.t === 'c') {
        if (a.f !== b.f || a.a.length !== b.a.length) return null;
        let code = '';
        for (let i = 0; i < a.a.length; i++) { const c = unify(a.a[i], b.a[i], s, fail); if (c === null) return null; code += c; }
        return code;
      }
      return sameTerm(a, b) ? '' : null;
    }
    // an integer against a pattern: only an equal integer constant unifies
    function intMatch(v, pat, fail) {
      pat = D(pat);
      if (pat.t === 'n' && !pat.f) return 'if (' + v + ' ' + EM.NEOP + ' ' + EM.num(pat.v) + ') ' + fail + '\n';
      return fail + '\n';
    }
    // integer arithmetic on ground values; unbox bails on anything but an integer
    const OPS = { '+': 'IADD', '-': 'ISUB', '*': 'IMUL' };
    const FNS = { '//': 'IDIV', mod: 'IMOD', rem: 'IREM', min: 'MIN', max: 'MAX' };
    function arith(t, s) {
      t = D(t);
      if (t.t === 'n') { if (t.f || !Number.isSafeInteger(t.v)) nope(); return '(' + EM.num(t.v) + ')'; }
      if (t.t === 'v') { const x = get(s, t); if (x.k !== 'G') nope(); return x.int ? V(x) : EM.unbox(V(x)); }
      if (t.t !== 'c') nope();
      if (t.a.length === 2) {
        const a = arith(t.a[0], s), b = arith(t.a[1], s);
        if (OPS[t.f]) return EM.fn(OPS[t.f], [a, b]); // checked: overflow bails out
        if (FNS[t.f]) return EM.fn(FNS[t.f], [a, b]);
        nope();
      }
      if (t.a.length === 1 && t.f === '-') return EM.fn('ISUB', ['(0)', arith(t.a[0], s)]);
      if (t.a.length === 1 && t.f === 'abs') return EM.fn('ABS', [arith(t.a[0], s)]);
      nope();
    }
    const CMPN = { '=:=': EM.EQOP, '=\\=': EM.NEOP, '<': '<', '>': '>', '=<': '<=', '>=': '>=' };
    let intRet = outs.length === 1;
    const RET = s => {
      if (outs.length === 1) {
        const x = get(s, outs[0]);
        if (!(x.k === 'G' && x.int)) intRet = false;
        if (selfInt) { if (!(x.k === 'G' && x.int)) nope(); return EM.retOuts([V(x)], true); }
      }
      return EM.retOuts(outs.map(v => build(v, s)), false);
    };
    let lab = 0;
    // compile a goal; fail is the statement run when it fails; returns { code, out } (out = state after,
    // null when control never falls through)
    function G(g, s, fail) {
      g = D(g); const kk = P.key(g);
      if (kk === ',/2') {
        const gs = P.flatConj(g); let code = '', cur = s;
        for (const x of gs) { if (!cur) break; const r = G(x, cur, fail); code += r.code; cur = r.out; }
        return { code, out: cur };
      }
      if (kk === 'true/0') return { code: '', out: s };
      if (kk === 'fail/0' || kk === 'false/0') return { code: fail + '\n', out: null };
      if (kk === 'if_commit/3') {
        const L = 'c' + (lab++), ok = 'ok' + L, LF = EM.fail(L);
        const rc = G(g.a[0], clone(s), LF);
        const rt = rc.out ? G(g.a[1], rc.out, fail) : null;
        // a condition that cannot fail is just its code then the then-branch
        if (rt && !rc.code.includes(LF)) return { code: rc.code + rt.code, out: rt.out };
        const re = G(g.a[2], clone(s), fail);
        if (!rt) return { code: rc.code === LF + '\n' ? re.code : EM.blockNoThen(L, rc.code, re.code), out: re.out };
        // a single test:  if (test) else-branch, otherwise then-branch
        const one = rc.code.startsWith('if (') && rc.code.endsWith(') ' + LF + '\n') && rc.code.indexOf('\n') === rc.code.length - 1 ? rc.code.slice(4, rc.code.length - LF.length - 3) : null;
        if (one !== null && !one.includes(LF)) return { code: 'if (' + one + ') {\n' + re.code + '} else {\n' + rt.code + '}\n', out: join(rt.out, re.out) };
        return { code: EM.block(L, ok, rc.code, rt.code, re.code), out: join(rt.out, re.out) };
      }
      if (kk === 'var/1' || kk === 'nonvar/1') {
        const x = D(g.a[0]); const xs = x.t === 'v' ? get(s, x) : { k: 'G' };
        if (xs.k === 'U' || xs.k === 'P') nope();
        const isVar = xs.k === 'F';
        return (kk === 'var/1') === isVar ? { code: '', out: s } : { code: fail + '\n', out: null };
      }
      if (kk === '=/2' || kk === '\\==/2' || kk === '==/2') {
        const a = D(g.a[0]), b = D(g.a[1]);
        const sa = a.t === 'v' && get(s, a), sb = b.t === 'v' && get(s, b);
        const stat = x => x && (x.k === 'TOP' || x.k === 'S');
        if (stat(sa) || stat(sb) || isStatusAtom(a) || isStatusAtom(b)) return statusGoal(kk, a, b, s, fail);
        if (kk === '=/2') { const s2 = clone(s); const c = unify(a, b, s2, fail); if (c === null) return { code: fail + '\n', out: null }; return { code: c, out: s2 }; }
        if (!allG(a, s) || !allG(b, s)) nope();
        return { code: 'if (' + (kk === '==/2' ? '!' : '') + EM.eq(build(a, s), build(b, s)) + ') ' + fail + '\n', out: s };
      }
      if (kk === 'is/2') {
        const x = D(g.a[0]), e = arith(g.a[1], s);
        const s2 = clone(s);
        if (x.t === 'v' && get(s, x).k === 'F') return { code: EM.assign(G_(s2, x, true), e), out: s2 };
        return { code: 'if (' + arith(x, s) + ' ' + EM.NEOP + ' ' + e + ') ' + fail + '\n', out: s };
      }
      if (CMPN[g.f] && g.t === 'c' && g.a.length === 2) return { code: 'if (!(' + arith(g.a[0], s) + ' ' + CMPN[g.f] + ' ' + arith(g.a[1], s) + ')) ' + fail + '\n', out: s };
      // a tabled call (q__dm): the native call of q__d for that mode, memoised on its ground inputs
      const memo = g.t === 'c' && /__dm$/.test(g.f) && prog.preds.has(g.f.slice(0, -1) + '/' + g.a.length);
      if (memo || (g.t === 'c' && /__d$/.test(g.f) && prog.preds.has(kk))) {
        const dk = memo ? g.f.slice(0, -1) + '/' + g.a.length : kk;
        const as = g.a.slice(0, -1), Sx = D(g.a[g.a.length - 1]);
        let m = ''; const ins = [], os = [];
        for (const a of as) {
          const ad = D(a);
          if (ad.t === 'v' && get(s, ad).k === 'F' && !os.includes(ad)) { m += 'o'; os.push(ad); }
          else if (ad.t === 'v' && get(s, ad).k === 'G' && get(s, ad).int) { m += 'n'; ins.push(V(get(s, ad))); }
          else if (ad.t === 'n' && !ad.f && Number.isSafeInteger(ad.v)) { m += 'n'; ins.push(EM.num(ad.v)); }
          else if (allG(a, s)) { m += 'i'; ins.push(build(a, s)); }
          else nope();
        }
        if (os.some(v => as.filter(a => termVars(a).includes(v)).length > 1)) nope();
        const cinfo = need(dk, m), callee = cinfo.name;
        const s2 = clone(s);
        const outT = os.map(v => G_(s2, v, os.length === 1 && cinfo.retInt));
        const sx = get(s, Sx);
        const rs = 's' + (nl++); statusLocals.add(rs);
        const call = EM.call(callee, ins, outT, os.length === 1 && cinfo.retInt, rs, memo && os.length <= 1 ? { table: dk + '|' + m, mode: m } : null);
        if (sx.k === 'TOP') return { code: '{ ' + call + 'if (' + rs + ' ' + EM.NEOP + ' ' + EM.YES + ') ' + EM.retStatus(rs) + '\n' + RET(s2) + ' }\n', out: null };
        if (sx.k !== 'F') nope();
        s2.set(Sx, { k: 'S', js: rs, set: true });
        return { code: call, out: s2 };
      }
      nope();
    }
    // status variables: the top S returns; local ones are assigned once, then tested
    function statusGoal(kk, a, b, s, fail) {
      const val = (t, x) => isStatusAtom(t) ? ATOM[D(t).n] : x && x.k === 'S' && x.set ? x.js : null;
      let sa = D(a).t === 'v' ? get(s, D(a)) : null, sb = D(b).t === 'v' ? get(s, D(b)) : null;
      if (kk === '=/2') {
        if (sb && sb.k === 'TOP') { [a, b] = [b, a]; [sa, sb] = [sb, sa]; }
        if (sa && sa.k === 'TOP') {
          const v = val(b, sb); if (!v) nope();
          if (v === EM.YES) return { code: RET(s) + '\n', out: null };
          if (v === EM.NO || v === EM.MAYBE) return { code: EM.retStatus(v) + '\n', out: null };
          // after if_commit(S1 = yes, .., S = S1) the value cannot be yes, and the outputs need not exist
          let ret; const keep = intRet; try { ret = RET(s); } catch (e) { if (e !== NOPE) throw e; ret = EM.BAIL; intRet = keep; }
          return { code: 'if (' + v + ' ' + EM.EQOP + ' ' + EM.YES + ') { ' + ret + ' }\n' + EM.retStatus(v) + '\n', out: null };
        }
        if (sb && (sb.k === 'F') && !(sa && sa.k === 'F')) { [a, b] = [b, a]; [sa, sb] = [sb, sa]; }
        if (sa && sa.k === 'F') { // a fresh local status takes a value
          const v = val(b, sb); if (!v) nope();
          const sv = 's' + (nl++); statusLocals.add(sv);
          const s2 = clone(s); s2.set(D(a), { k: 'S', js: sv, set: true });
          return { code: sv + ' = ' + v + ';\n', out: s2 };
        }
        const va = val(a, sa), vb = val(b, sb); if (!va || !vb) nope();
        return { code: 'if (' + va + ' ' + EM.NEOP + ' ' + vb + ') ' + fail + '\n', out: s };
      }
      const va = val(a, sa), vb = val(b, sb); if (!va || !vb) nope();
      return { code: 'if (' + va + ' ' + (kk === '==/2' ? EM.NEOP : EM.EQOP) + ' ' + vb + ') ' + fail + '\n', out: s };
    }
    const body = G(cl.a[1], st, EM.BAIL);
    return { src: EM.func(fnName, params, outs.length, selfInt, [...used.values()], [...statusLocals], body.code), intRet };
  }

  // a batch: the root (k, mode) and every native function it calls that is not compiled yet, with the fixpoint
  // over which single-output functions return raw integers.  done: key -> { name, retInt } of earlier batches
  // (null when refused).  Returns Map key -> { name, src, retInt }, or null when refused.
  function nativeBatch(prog, k, mode, EM, done, newName) {
    let batch = new Map();
    const retInt = new Map();
    try {
      const need = (k2, m2) => {
        const key2 = k2 + '|' + m2;
        if (done.has(key2)) { const f = done.get(key2); if (!f) nope(); return { name: f.ref, retInt: !!f.retInt }; }
        if (batch.has(key2)) return { name: batch.get(key2).name, retInt: !!retInt.get(key2) };
        const name = newName(key2);
        const ent = { name, src: null }; batch.set(key2, ent);
        const g = genNative(prog, k2, m2, name, need, !!retInt.get(key2), EM);
        ent.src = g.src; ent.intRet = g.intRet; ent.k = k2; ent.mode = m2;
        return { name, retInt: !!retInt.get(key2) };
      };
      for (let pass = 0; ; pass++) {
        batch = new Map(); EM.reset && EM.reset(); need(k, mode);
        let changed = false;
        for (const [key2, e] of batch) if (e.intRet !== !!retInt.get(key2)) { retInt.set(key2, e.intRet); changed = true; }
        if (!changed) break;
        if (pass > 6) nope();
      }
      for (const [key2, e] of batch) e.retInt = !!retInt.get(key2);
      return batch;
    } catch (e) {
      if (e !== NOPE) throw e;
      if (P.NATIVE_DEBUG) console.log('native refused', k + '|' + mode, P.NATIVE_WHY);
      return null;
    }
  }
  P.nativeGen = genNative;
  P.nativeBatch = nativeBatch;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog fast Detlog engine: a closure-compiled deterministic interpreter.
   Determinism is what makes it fast:
   - each clause is compiled once into closures (no copying of clause bodies at call time);
   - heads are matched WAM-style: a first-occurrence head variable takes the argument itself,
     so nothing is copied or bound to enter a clause;
   - a call selects its clause by first argument and commits: no choicepoint, no retry, and the
     trail is only consulted by if_commit/3 conditions;
   - the generated packet loops ( nm([],[]).  nm([I|Is],O) :- nmr(I,O1), nm(Is,O2), rows_concat([O1,O2],O). )
     run as native loops in linear time.
   Its answers are those of the reference Detlog engine (detlog_engine.js); a run that exhausts the JS
   stack falls back to it. */
(function (P) {
  if (!P.nativeBatch && typeof require === 'function') require('./native.js');
  'use strict';
  const { Var, Cmp, NIL, list, deref, listToArray, termVars } = P;
  const D = deref;

  function FastDetlog(prog, opts) {
    this.prog = prog; this.opts = opts || {};
    this.preds = new Map();      // key -> {fn}
    const self = this;
    for (const [k, cls] of prog.preds) this.ref(k).fn = this.compilePred(k, cls);
  }
  FastDetlog.prototype.ref = function (k) { let r = this.preds.get(k); if (!r) { r = { fn: null, k }; this.preds.set(k, r); } return r; };

  // the machine state lives on a DetEngine (trail, unify, steps, memo, output), so runtime builtins are shared
  FastDetlog.prototype.compilePred = function (k, cls) {
    const self = this;
    const loop = this.loopIdiom(k, cls);
    if (loop) return loop;
    const cc = cls.map(cl => this.compileClause(cl));
    const n = cls[0] && D(cls[0].head).t === 'c' ? D(cls[0].head).a.length : 0;
    // first-argument index: key -> clause list (clauses with a variable first argument go everywhere, in order)
    const keyOf = t => { t = D(t); return t.t === 'c' ? 'c' + t.f + '/' + t.a.length : t.t === 'a' ? 'a' + t.n : t.t === 'n' ? 'n' + t.v + (t.f ? 'f' : '') : t.t === 's' ? 's' + t.v : null; };
    const heads = cls.map(cl => n ? keyOf(D(cl.head).a[0]) : null);
    const index = new Map(); const varIdx = [];
    heads.forEach((h, i) => { if (h === null) varIdx.push(i); });
    for (const h of new Set(heads.filter(x => x !== null))) index.set(h, heads.map((x, i) => (x === h || x === null) ? i : -1).filter(i => i >= 0));
    const all = cc.map((_, i) => i);
    const single = cc.length === 1 ? cc[0] : null;
    return function (args, E) {
      E.tick();
      let cand;
      if (single) cand = null;
      else if (!n) cand = all;
      else {
        const a0 = D(args[0]);
        if (a0.t === 'v') cand = all;
        else cand = index.get(keyOf(a0)) || varIdx;
        if (cand.length > 1 && E.violations.length < 1000) E.violations.push(k);
      }
      if (single) {
        const env = new Array(single.nslots); const m = E.trail.length;
        if (single.head(args, env, E)) return single.body(env, E);
        E.undo(m); return false;
      }
      for (let j = 0; j < cand.length; j++) {
        const c = cc[cand[j]];
        const env = new Array(c.nslots); const m = E.trail.length;
        if (c.head(args, env, E)) return c.body(env, E);
        E.undo(m);
      }
      return false;
    };
  };

  FastDetlog.prototype.compileClause = function (cl) {
    const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
    const vars = termVars(Cmp('-', [cl.head, cl.body]));
    const slot = new Map(); vars.forEach((v, i) => slot.set(v, i));
    const seen = new Set();
    const matchers = hargs.map(h => this.compileMatch(h, slot, seen));
    const nh = matchers.length;
    const headFn = nh === 0 ? () => true : function (args, env, E) { for (let i = 0; i < nh; i++) if (!matchers[i](args[i], env, E)) return false; return true; };
    const body = this.compileGoal(cl.body, slot);
    return { head: headFn, body, nslots: vars.length };
  };

  function isGroundTerm(t) { return P.isGround(t); }
  function markGround(t) { t = D(t); if (t.t === 'c' && !t.gr) { t.gr = true; t.a.forEach(markGround); } }
  FastDetlog.prototype.compileBuild = function (t, slot) {
    t = D(t);
    if (t.t === 'v') { const i = slot.get(t); const nm = t.name; return env => env[i] || (env[i] = Var(nm)); }
    if (t.t !== 'c' || isGroundTerm(t)) { if (t.t === 'c') markGround(t); return () => t; }
    const f = t.f, bs = t.a.map(x => this.compileBuild(x, slot)), n = bs.length;
    if (n === 2) { const b0 = bs[0], b1 = bs[1]; return env => ({ t: 'c', f, a: [b0(env), b1(env)] }); }
    return env => { const a = new Array(n); for (let i = 0; i < n; i++) a[i] = bs[i](env); return { t: 'c', f, a }; };
  };
  FastDetlog.prototype.compileMatch = function (h, slot, seen) {
    h = D(h);
    if (h.t === 'v') {
      const i = slot.get(h);
      if (!seen.has(h)) { seen.add(h); return (a, env) => { env[i] = a; return true; }; }
      return (a, env, E) => E.unify(env[i], a);
    }
    if (h.t === 'a') return (a, env, E) => { a = D(a); if (a.t === 'v') { E.bind(a, h); return true; } return a === h || (a.t === 'a' && a.n === h.n); };
    if (h.t === 'n') return (a, env, E) => { a = D(a); if (a.t === 'v') { E.bind(a, h); return true; } return a.t === 'n' && a.v === h.v && a.f === h.f; };
    if (h.t === 's') return (a, env, E) => { a = D(a); if (a.t === 'v') { E.bind(a, h); return true; } return a.t === 's' && a.v === h.v; };
    // compound: build it when the argument is a variable, otherwise match argument by argument
    const build = this.compileBuild(h, slot);
    const subs = h.a.map(x => this.compileMatch(x, slot, seen));
    const f = h.f, n = h.a.length;
    return (a, env, E) => {
      a = D(a);
      if (a.t === 'v') { E.bind(a, build(env)); return true; }
      if (a.t !== 'c' || a.f !== f || a.a.length !== n) return false;
      for (let i = 0; i < n; i++) if (!subs[i](a.a[i], env, E)) return false;
      return true;
    };
  };

  FastDetlog.prototype.compileGoal = function (g, slot) {
    g = D(g);
    const self = this;
    const k = P.key(g);
    if (k === ',/2') {
      const gs = P.flatConj(g).map(x => this.compileGoal(x, slot)); const n = gs.length;
      return (env, E) => { for (let i = 0; i < n; i++) if (!gs[i](env, E)) return false; return true; };
    }
    if (k === 'true/0') return (env, E) => { E.tick(); return true; };
    if (k === 'fail/0' || k === 'false/0') return (env, E) => { E.tick(); return false; };
    if (k === 'if_commit/3') {
      const C = this.compileGoal(g.a[0], slot), T = this.compileGoal(g.a[1], slot), F = this.compileGoal(g.a[2], slot);
      return (env, E) => { E.tick(); E.decisions++; const m = E.trail.length; if (C(env, E)) return T(env, E); E.undo(m); return F(env, E); };
    }
    if (k === '=/2') { // inline unification
      const a = this.compileBuild(g.a[0], slot), b = this.compileBuild(g.a[1], slot);
      return (env, E) => { E.tick(); const m = E.trail.length; if (E.unify(a(env), b(env))) return true; E.undo(m); return false; };
    }
    const as = g.t === 'c' ? g.a.map(x => this.compileBuild(x, slot)) : []; const n = as.length;
    const build = env => { const a = new Array(n); for (let i = 0; i < n; i++) a[i] = as[i](env); return a; };
    if (this.prog.preds.has(k)) {
      const r = this.ref(k);
      return (env, E) => r.fn(build(env), E);
    }
    const rb = P.DETLOG_RUNTIME[k] || (P.builtins[k] && !P.builtins[k].nondet && !P.builtins[k].call ? P.builtins[k].fn : null);
    if (rb) return (env, E) => { E.tick(); const a = build(env); const m = E.trail.length; if (rb(a, E)) return true; E.undo(m); return false; };
    return () => { throw new Error('Detlog engine: unknown procedure ' + k); };
  };

  // the generated packet loop, run as a native loop
  FastDetlog.prototype.loopIdiom = function (k, cls) {
    const sh = loopShape(k, cls); if (!sh) return null;
    const r = this.ref(sh.callKey), cutVariant = sh.cutVariant;
    return function (args, E) {
      E.tick();
      const items = listToArray(args[0]);
      if (!items) return false;
      const out = [];
      for (let i = 0; i < items.length; i++) {
        E.tick(2);
        const Ov = Var();
        if (!r.fn([items[i], Ov], E)) return false;
        const o1 = listToArray(Ov); E.tick(o1.length);
        let hasCut = false;
        for (const x of o1) { out.push(x); if (cutVariant && D(x).t === 'a' && D(x).n === 'cut') hasCut = true; }
        if (cutVariant && hasCut) { const it = D(items[i]); if (it.t === 'c' && it.f === 'e') break; }
      }
      return E.unify(args[1], list(out));
    };
  };
  function loopShape(k, cls) {
    if (cls.length !== 2 || !/\/2$/.test(k)) return null;
    const [c1, c2] = cls.map(c => ({ h: D(c.head), b: P.flatConj(c.body).map(D) }));
    const nm = c1.h.f;
    if (!(P.isNil(D(c1.h.a[0])) && P.isNil(D(c1.h.a[1])) && c1.b.length === 1 && P.key(c1.b[0]) === 'true/0')) return null;
    const h0 = D(c2.h.a[0]); if (!(P.isCons(h0) && D(h0.a[0]).t === 'v' && D(h0.a[1]).t === 'v')) return null;
    const I = D(h0.a[0]), Is = D(h0.a[1]), O = D(c2.h.a[1]); if (O.t !== 'v') return null;
    const b = c2.b; if (b.length < 2) return null;
    const call = b[0]; if (call.t !== 'c' || call.a.length !== 2 || D(call.a[0]) !== I || D(call.a[1]).t !== 'v') return null;
    const O1 = D(call.a[1]);
    const isRec = (g, O2) => g.t === 'c' && g.f === nm && g.a.length === 2 && D(g.a[0]) === Is && D(g.a[1]) === O2;
    const isCat = (g, O2, Out) => { if (P.key(g) !== 'rows_concat/2') return false; const l = listToArray(g.a[0]); return l && l.length === 2 && D(l[0]) === O1 && D(l[1]) === O2 && D(g.a[1]) === Out; };
    let cutVariant = false;
    if (b.length === 3) { const O2 = D(b[1].a && b[1].a[1]); if (!(isRec(b[1], O2) && isCat(b[2], O2, O))) return null; }
    else if (b.length === 2 && P.key(b[1]) === 'if_commit/3') {
      const ic = b[1]; const cnd = D(ic.a[0]), t = D(ic.a[1]), e = P.flatConj(ic.a[2]).map(D);
      if (!(P.key(cnd) === 'cut_in/2' && D(cnd.a[0]) === I && D(cnd.a[1]) === O1 && P.key(t) === '=/2' && D(t.a[0]) === O && D(t.a[1]) === O1 && e.length === 2)) return null;
      const O2 = D(e[0].a && e[0].a[1]); if (!(isRec(e[0], O2) && isCat(e[1], O2, O))) return null;
      cutVariant = true;
    } else return null;
    return { callKey: P.key(call), cutVariant };
  }

  // ---------------- JIT: Detlog compiled to JavaScript source ----------------
  // One JS function per predicate with positional arguments; clause variables are JS locals; heads are matched
  // inline; if_commit/3 is a labelled block.  Step counts, clause selection and violation counts are those of the
  // closure compiler above, which remains the fallback.
  function jitCompile(prog) {
    const consts = [], constIdx = new Map();
    const K = t => { let i = constIdx.get(t); if (i === undefined) { i = consts.length; consts.push(t); constIdx.set(t, i); } return 'K[' + i + ']'; };
    const rbs = [], rbIdx = new Map();
    const RBf = k => { let i = rbIdx.get(k); if (i === undefined) { const f = P.DETLOG_RUNTIME[k] || (P.builtins[k] && !P.builtins[k].nondet && !P.builtins[k].call ? P.builtins[k].fn : null); if (!f) return null; i = rbs.length; rbs.push(f); rbIdx.set(k, i); } return 'RB[' + i + ']'; };
    const fname = new Map(); let pi = 0;
    for (const k of prog.preds.keys()) fname.set(k, 'p' + (pi++));
    const arityOf = k => +k.slice(k.lastIndexOf('/') + 1);
    let lab = 0;
    let mentioned = new Set(); // variables that occur textually before the goal being compiled
    const out = [];
    const TICK = 'if (++E.steps > E.stepLimit) OVER(E);';
    function keyTest(h, x) {
      if (h.t === 'v') return 'true';
      if (h.t === 'a') return x + ' === ' + K(h);
      if (h.t === 'n') return '(' + x + '.t === "n" && ' + x + '.v === ' + numLit(h.v) + ' && ' + x + '.f === ' + !!h.f + ')';
      if (h.t === 's') return '(' + x + '.t === "s" && ' + x + '.v === ' + JSON.stringify(h.v) + ')';
      return '(' + x + '.t === "c" && ' + x + '.f === ' + JSON.stringify(h.f) + ' && ' + x + '.a.length === ' + h.a.length + ')';
    }
    function numLit(v) { return Number.isFinite(v) ? String(v) : (v > 0 ? 'Infinity' : v < 0 ? '-Infinity' : 'NaN'); }
    // a clause: inline (single-clause predicate: head failure returns false) or fn (head failure returns undefined)
    function genClause(cl, ci, A) {
      const vars = termVars(Cmp('-', [cl.head, cl.body]));
      const slot = new Map(); vars.forEach((v, i) => slot.set(v, i));
      const decl = vars.length ? 'let ' + vars.map((_, i) => 'v' + i).join(', ') + ';\n' : '';
      const seen = new Set();
      const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
      const mk = (headFail) => {
        seen.clear(); let d = 0;
        const match = (h, x) => {
          h = D(h);
          if (h.t === 'v') { const i = slot.get(h); if (!seen.has(h)) { seen.add(h); return 'v' + i + ' = ' + x + ';\n'; } return 'if (!E.unify(v' + i + ', ' + x + ')) ' + headFail + '\n'; }
          const t = 'h' + (d++);
          if (h.t !== 'c') return '{ const ' + t + ' = D(' + x + '); if (' + t + '.t === "v") E.bind(' + t + ', ' + K(h) + '); else if (!(' + keyTest(h, t) + ')) ' + headFail + ' }\n';
          // the build branch creates the pattern's new variables lazily, the match branch assigns them:
          // either way they are defined afterwards, so first occurrences are tracked once, in order
          const b = build(h, slot);
          let sub = '';
          h.a.forEach((y, i) => { sub += match(y, t + '.a[' + i + ']'); });
          return '{ const ' + t + ' = D(' + x + ');\nif (' + t + '.t === "v") E.bind(' + t + ', ' + b + ');\nelse if (' + t + '.t === "c" && ' + t + '.f === ' + JSON.stringify(h.f) + ' && ' + t + '.a.length === ' + h.a.length + ') {\n' + sub + '} else ' + headFail + ' }\n';
        };
        let code = '';
        hargs.forEach((h, i) => { code += match(h, A[i]); });
        return code;
      };
      const bodyCode = (fail) => { mentioned = new Set(termVars(cl.head)); return goal(cl.body, slot, fail); };
      const inlineHead = mk('{ E.undo(m0); return false; }');
      const inl = decl + 'const m0 = E.trail.length;\n' + inlineHead + bodyCode('return false;') + 'return true;';
      const fnHead = mk('{ E.undo(m0); return undefined; }');
      const fn = decl + 'const m0 = E.trail.length;\n' + fnHead + bodyCode('return false;') + 'return true;';
      return { inline: inl, fn };
    }
    function build(t, slot) {
      t = D(t);
      if (t.t === 'v') { const i = slot.get(t); return '(v' + i + ' || (v' + i + ' = V(' + JSON.stringify(t.name) + ')))'; }
      if (t.t !== 'c' || P.isGround(t)) { if (t.t === 'c') markGround(t); return K(t); }
      return '{t: "c", f: ' + JSON.stringify(t.f) + ', a: [' + t.a.map(x => build(x, slot)).join(', ') + ']}';
    }
    const mention = t => { for (const v of termVars(t)) mentioned.add(v); };
    const ARITH2 = { '+': '+', '-': '-', '*': '*' };
    const CMP = { '=:=/2': '===', '=\\=/2': '!==', '</2': '<', '>/2': '>', '=</2': '<=', '>=/2': '>=' };
    // an integer expression compiled to JS: leaves are integers or variables, operators + - * and unary -;
    // a leaf that is not a safe integer, or a result that is not, sets bad, and the generic builtin runs
    // instead (errors, floats, integers beyond 2^53)
    function arith(t, slot) {
      t = D(t);
      if (t.t === 'n') return t.f || !Number.isSafeInteger(t.v) ? null : '(' + t.v + ')';
      if (t.t === 'v') { const i = slot.get(t); return '((q = D(v' + i + ' || BADV)).t === "n" && !q.f && typeof q.v === "number" ? q.v : (bad = true, 0))'; }
      if (t.t !== 'c') return null;
      // each result must stay a safe integer, or the generic builtin (unbounded integers) runs instead
      if (t.a.length === 2 && ARITH2[t.f]) { const a = arith(t.a[0], slot), b = arith(t.a[1], slot); return a && b ? '(Number.isSafeInteger(q2 = ' + a + ' ' + ARITH2[t.f] + ' ' + b + ') ? q2 : (bad = true, 0))' : null; }
      if (t.a.length === 1 && t.f === '-') { const a = arith(t.a[0], slot); return a ? '(-' + a + ')' : null; }
      return null;
    }
    function goal(g, slot, FAIL) {
      const code = goal0(g, slot, FAIL); mention(g); return code;
    }
    // builtin_rows(member(X, L), P), splice_extend(P, [member(X, L)], Env, R), with P used nowhere else:
    // for each element Y of the proper list L, unify X = Y in place, copy Env, undo.  This is what the two goals
    // compute (each row is the goal's instance; unifying it back binds X and nothing else that is observable).
    function fuseGen(g1, g2, rest, slot, FAIL) {
      if (P.key(g1) !== 'builtin_rows/2' || P.key(g2) !== 'splice_extend/4') return null;
      const G = D(g1.a[0]), Pv = D(g1.a[1]);
      const gk = P.key(G);
      if ((gk !== 'member/2' && gk !== 'permutation/2') || Pv.t !== 'v' || D(g2.a[0]) !== Pv) return null;
      const pat = P.listToArray(g2.a[1]); if (!pat || pat.length !== 1 || P.show(pat[0]) !== P.show(G) || !sameTerm(pat[0], G)) return null;
      if (rest.some(x => termVars(x).includes(Pv)) || termVars(g2.a[2]).includes(Pv) || termVars(g2.a[3]).includes(Pv) || mentioned.has(Pv)) return null;
      const generic = goal0(g1, slot, FAIL) + goal0(g2, slot, FAIL);
      if (gk === 'permutation/2') {
        // permutation(Xs, Ys) with Xs a proper list: the builtin's order (each element first in turn, then the
        // permutations of the rest), each permutation unified with Ys, the environment copied, undone
        return '{ const xs = LA(' + build(G.a[0], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' + TICK + ' ' + TICK + '\nconst y = ' + build(G.a[1], slot) + ', env = ' + build(g2.a[2], slot) + ', res = [];\n' +
          'PERMS(xs, p => { const m = E.trail.length; if (E.unify(y, p)) { E.steps += 2; if (E.steps > E.stepLimit) OVER(E); res.push(COPY(env)); if (res.length > 1e6) throw new LIMIT("builtin_rows: infinite generator permutation/2 (no finite packet)"); } E.undo(m); });\n' +
          'E.rowsBuilt += res.length; if (res.length > E.maxRows) E.maxRows = res.length;\n' +
          '{ const m = E.trail.length; if (!E.unify(' + build(g2.a[3], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
      }
      // steps as the two goals count them: one per call and one per solution, for each of the two
      return '{ const xs = LA(' + build(G.a[1], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' + TICK + ' ' + TICK + '\nconst x = ' + build(G.a[0], slot) + ', env = ' + build(g2.a[2], slot) + ', res = [];\n' +
        'for (let i = 0; i < xs.length; i++) { const m = E.trail.length; if (E.unify(x, xs[i])) { E.steps += 2; if (E.steps > E.stepLimit) OVER(E); res.push(COPY(env)); } E.undo(m); }\n' +
        'E.rowsBuilt += res.length; if (res.length > E.maxRows) E.maxRows = res.length;\n' +
        '{ const m = E.trail.length; if (!E.unify(' + build(g2.a[3], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
    }
    // generator, splice and row loop in one loop:
    //   builtin_rows(G, P), splice_extend(P, [G], e(Env), R2), loop(R2, R1)
    // with G member/2 or permutation/2 over a proper list, loop a packet loop (no cut) whose row predicate
    // starts by copying its row: each solution is bound in place, the row predicate runs on the environment
    // directly (it copies it first), its rows are copied (they may hold variables bound inside the row
    // predicate) and kept, and the binding is undone.  Same rows in the same order,
    // with the steps the three goals count; the list of rows R2 is never built.
    function fuseGenLoop(g1, g2, g3, rest, slot, FAIL) {
      if (P.key(g1) !== 'builtin_rows/2' || P.key(g2) !== 'splice_extend/4') return null;
      const G = D(g1.a[0]), Pv = D(g1.a[1]), gk = P.key(G);
      if ((gk !== 'member/2' && gk !== 'permutation/2') || Pv.t !== 'v' || D(g2.a[0]) !== Pv) return null;
      const pat = P.listToArray(g2.a[1]); if (!pat || pat.length !== 1 || !sameTerm(pat[0], G)) return null;
      const R2 = D(g2.a[3]); if (R2.t !== 'v' || D(g3.a ? g3.a[0] : null) !== R2 || !g3.a || g3.a.length !== 2) return null;
      const k3 = P.key(g3); const lcls = prog.preds.get(k3); if (!lcls) return null;
      const sh = loopShape(k3, lcls); if (!sh || sh.cutVariant || !fname.has(sh.callKey)) return null;
      // the row predicate's row clause must copy its row before anything else
      const rcl = (prog.preds.get(sh.callKey) || []).find(c => isC(D(c.head).a[0], 'e', 1));
      if (!rcl || P.key(D(P.flatConj(rcl.body)[0])) !== 'copy_term/2' || D(D(P.flatConj(rcl.body)[0]).a[0]) !== D(D(D(rcl.head).a[0]).a[0])) return null;
      const used = rest.concat([g3.a[1]]).some(x => termVars(x).some(v => v === Pv || v === R2)) || termVars(g2.a[2]).includes(R2) || mentioned.has(Pv) || mentioned.has(R2);
      if (used) return null;
      const env = g2.a[2]; if (!isC(env, 'e', 1)) return null;
      const generic = goal0(g1, slot, FAIL) + goal0(g2, slot, FAIL) + goal0(g3, slot, FAIL);
      const rf = fname.get(sh.callKey);
      // a DET filter as the row predicate:
      //   r(e(W), O) :- copy_term(W, L), if_commit((q__d(As.., S), S \== maybe), if_commit(S = yes, O = [e(L)], O = []), Packet)
      // the native q__d runs on the solution in place; only a kept row is copied.  Without a native function
      // (or when it declines) the row predicate runs as above.
      let filt = null;
      { const rb = P.flatConj(rcl.body).map(D);
        const Lr = P.listToArray(rb[0].a[1]), Ev = P.listToArray(D(env).a[0]);
        const ic = rb[1];
        if (rb.length === 2 && Lr && Ev && Lr.length === Ev.length && Lr.every(v => D(v).t === 'v') && P.key(ic) === 'if_commit/3') {
          const c = P.flatConj(ic.a[0]).map(D), th = D(ic.a[1]);
          if (c.length === 2 && c[0].t === 'c' && /__d$/.test(c[0].f) && P.key(c[1]) === '\\==/2' && D(c[1].a[0]) === D(c[0].a[c[0].a.length - 1]) && P.key(th) === 'if_commit/3') {
            const Sv = D(c[0].a[c[0].a.length - 1]);
            const yes = D(th.a[0]), keep = D(th.a[1]), drop = D(th.a[2]);
            const Orow = D(D(rcl.head).a[1]);
            const okYes = P.key(yes) === '=/2' && D(yes.a[0]) === Sv && D(yes.a[1]).t === 'a' && D(yes.a[1]).n === 'yes';
            const okKeep = P.key(keep) === '=/2' && D(keep.a[0]) === Orow && sameTerm(keep.a[1], P.list([P.Cmp('e', [P.list(Lr)])]));
            const okDrop = P.key(drop) === '=/2' && D(drop.a[0]) === Orow && D(drop.a[1]).t === 'a' && D(drop.a[1]).n === '[]';
            // the call's arguments, over the loop's environment instead of the row's copy
            const sub = new Map(Lr.map((v, i) => [D(v), Ev[i]]));
            const subst = t => { t = D(t); if (t.t === 'v') return sub.has(t) ? sub.get(t) : null; if (t.t === 'c') { const a = t.a.map(subst); return a.includes(null) ? null : P.Cmp(t.f, a); } return t; };
            const args = c[0].a.slice(0, -1).map(subst);
            if (okYes && okKeep && okDrop && !args.includes(null)) filt = { k: P.key(c[0]), args };
          }
        } }
      if (filt) {
        // permutation(Xs, Ys) filtered by a pairwise test on Ys (when the program's source is known, as
        // prog.pairwiseSource): failing prefixes are dropped (src/algebra.js has the derivation)
        let pwEach = null;
        if (gk === 'permutation/2' && prog.pairwiseSource && P.pairwise && filt.args.length === 1 && D(filt.args[0]) === D(G.a[1]) && /__d\/\d+$/.test(filt.k)) {
          const pw = P.pairwise(prog.pairwiseSource, filt.k.replace(/__d\/(\d+)$/, (_, a) => '/' + (+a - 1)));
          if (pw) pwEach = '(fn) => PERMSPW(xs, (p, yv, dist) => ' + pw.code('p', 'yv', 'dist', true) + ', ' + pw.c0 + ', fn)';
        }
        const each = gk === 'member/2' ? '(fn) => { for (let i = 0; i < xs.length; i++) fn(xs[i]); }' : pwEach || '(fn) => PERMS(xs, fn)';
        const argsCode = filt.args.map(a => build(a, slot)).join(', ');
        return '{ const xs = LA(' + build(G.a[1 - (gk === 'member/2' ? 0 : 1)], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' +
          TICK + ' ' + TICK + ' ' + TICK + '\nconst x = ' + build(G.a[gk === 'member/2' ? 0 : 1], slot) + ', ev = ' + build(env, slot) + ', res = []; let ok = true, nrow = 0;\n' +
          '(' + each + ')(y => { if (!ok) return; const m = E.trail.length; if (E.unify(x, y)) { E.steps += 4; if (E.steps > E.stepLimit) OVER(E); if (++nrow > 1e6) throw new LIMIT("builtin_rows: infinite generator ' + gk + ' (no finite packet)"); ' +
          'const Sv = V(null); const h = NATE(' + JSON.stringify(filt.k) + ', [' + argsCode + (argsCode ? ', ' : '') + 'Sv], E);\n' +
          'if (h === true) { E.steps += 1; if (D(Sv).n === "yes") res.push(COPY(ev)); }\n' +
          'else { const Ov = V(null); if (!' + rf + '(ev, Ov, E)) ok = false; else { const o1 = LA(Ov); E.steps += (o1.length || 1); if (E.steps > E.stepLimit) OVER(E); for (let j = 0; j < o1.length; j++) res.push(COPY(o1[j])); } } } E.undo(m); });\n' +
          'E.rowsBuilt += nrow; if (nrow > E.maxRows) E.maxRows = nrow;\n' +
          'if (!ok) { ' + FAIL + ' }\n{ const m = E.trail.length; if (!E.unify(' + build(g3.a[1], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
      }
      const each = gk === 'member/2'
        ? '(fn) => { for (let i = 0; i < xs.length; i++) fn(xs[i]); }'
        : '(fn) => PERMS(xs, fn)';
      return '{ const xs = LA(' + build(G.a[1 - (gk === 'member/2' ? 0 : 1)], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' +
        TICK + ' ' + TICK + ' ' + TICK + '\nconst x = ' + build(G.a[gk === 'member/2' ? 0 : 1], slot) + ', ev = ' + build(env, slot) + ', res = []; let ok = true, nrow = 0;\n' +
        '(' + each + ')(y => { if (!ok) return; const m = E.trail.length; if (E.unify(x, y)) { E.steps += 4; if (E.steps > E.stepLimit) OVER(E); if (++nrow > 1e6) throw new LIMIT("builtin_rows: infinite generator ' + gk + ' (no finite packet)"); const Ov = V(null); if (!' + rf + '(ev, Ov, E)) ok = false; else { const o1 = LA(Ov); E.steps += (o1.length || 1); if (E.steps > E.stepLimit) OVER(E); for (let j = 0; j < o1.length; j++) res.push(COPY(o1[j])); } } E.undo(m); });\n' +
        'E.rowsBuilt += nrow; if (nrow > E.maxRows) E.maxRows = nrow;\n' +
        'if (!ok) { ' + FAIL + ' }\n{ const m = E.trail.length; if (!E.unify(' + build(g3.a[1], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
    }
    function isC(t, f, n) { t = D(t); return t.t === 'c' && t.f === f && t.a.length === n; }
    function sameTerm(a, b) { a = D(a); b = D(b); if (a === b) return true; if (a.t !== b.t) return false; if (a.t === 'c') return a.f === b.f && a.a.length === b.a.length && a.a.every((x, i) => sameTerm(x, b.a[i])); if (a.t === 'a') return a === b; if (a.t === 'n') return a.v === b.v && a.f === b.f; if (a.t === 's') return a.v === b.v; return false; }
    function goal0(g, slot, FAIL) {
      g = D(g); const k = P.key(g);
      if (k === 'is/2' || CMP[k]) {
        const rb = RBf(k);
        const generic = '{ const m = E.trail.length; if (!' + rb + '([' + g.a.map(x => build(x, slot)).join(', ') + '], E)) { E.undo(m); ' + FAIL + ' } }';
        if (k === 'is/2') {
          const ex = arith(g.a[1], slot);
          if (ex) return TICK + '\n{ let bad = false, q, q2; const r = ' + ex + ';\nif (bad) ' + generic + '\nelse { const m = E.trail.length; if (!E.unify(' + build(g.a[0], slot) + ', INT(r))) { E.undo(m); ' + FAIL + ' } } }\n';
        } else {
          const ea = arith(g.a[0], slot), eb = arith(g.a[1], slot);
          if (ea && eb) return TICK + '\n{ let bad = false, q, q2; const x = ' + ea + ', y = ' + eb + ';\nif (bad) ' + generic + '\nelse if (!(x ' + CMP[k] + ' y)) ' + FAIL + ' }\n';
        }
      }
      if (k === 'copy_term/2') {
        // copy_term(Ts, [V1..Vn]) with V1..Vn distinct variables not seen before: assign the copies
        const dst = P.listToArray(g.a[1]), src = P.listToArray(g.a[0]);
        const fresh = dst && dst.every((v, i) => { v = D(v); return v.t === 'v' && !mentioned.has(v) && dst.findIndex(w => D(w) === v) === i; }) && !termVars(g.a[0]).some(v => dst.some(w => D(w) === v));
        if (fresh && src && dst.length === src.length) {
          return TICK + '\n{ const mp = new Map(); ' + dst.map((v, i) => 'v' + slot.get(D(v)) + ' = COPY(' + build(src[i], slot) + ', mp);').join(' ') + ' }\n';
        }
        // copy_term(Row, [V1..Vn]): copy the row once; a proper list of n items is assigned, anything else unifies
        if (fresh && !src) {
          const rb = RBf(k);
          return TICK + '\n{ const c = COPY(' + build(g.a[0], slot) + '); const ca = LA(c);\nif (ca && ca.length === ' + dst.length + ') { ' + dst.map((v, i) => 'v' + slot.get(D(v)) + ' = ca[' + i + '];').join(' ') + ' }\nelse { const m = E.trail.length; if (!E.unify(c, ' + build(g.a[1], slot) + ')) { E.undo(m); ' + FAIL + ' } } }\n';
        }
      }
      if (k === ',/2') {
        const gs = P.flatConj(g).map(D); let code = '';
        for (let i = 0; i < gs.length; i++) {
          const f3 = i + 2 < gs.length && fuseGenLoop(gs[i], gs[i + 1], gs[i + 2], gs.slice(i + 3), slot, FAIL);
          if (f3) { code += f3; mention(gs[i]); mention(gs[i + 1]); mention(gs[i + 2]); i += 2; continue; }
          const f = i + 1 < gs.length && fuseGen(gs[i], gs[i + 1], gs.slice(i + 2), slot, FAIL);
          if (f) { code += f; mention(gs[i]); mention(gs[i + 1]); i++; continue; }
          code += goal(gs[i], slot, FAIL);
        }
        return code;
      }
      if (k === 'true/0') return TICK + '\n';
      if (k === 'fail/0' || k === 'false/0') return TICK + ' ' + FAIL + '\n';
      if (k === 'if_commit/3') {
        const L = 'L' + (lab++);
        return TICK + ' E.decisions++;\n{ const m' + L + ' = E.trail.length; let ok' + L + ' = false;\n' + L + ': {\n' + goal(g.a[0], slot, 'break ' + L + ';') + 'ok' + L + ' = true;\n}\nif (ok' + L + ') {\n' + goal(g.a[1], slot, FAIL) + '} else {\nE.undo(m' + L + ');\n' + goal(g.a[2], slot, FAIL) + '}\n}\n';
      }
      if (k === '=/2') return TICK + '\n{ const m = E.trail.length; if (!E.unify(' + build(g.a[0], slot) + ', ' + build(g.a[1], slot) + ')) { E.undo(m); ' + FAIL + ' } }\n';
      const as = g.t === 'c' ? g.a.map(x => build(x, slot)) : [];
      if (prog.preds.has(k)) {
        if (/__d$/.test(g.f) && !/__d$/.test(curPred)) return '{ const h = NATE(' + JSON.stringify(k) + ', [' + as.join(', ') + '], E); if (h === undefined && !' + fname.get(k) + '(' + as.concat(['E']).join(', ') + ')) ' + FAIL + ' }\n';
        return 'if (!' + fname.get(k) + '(' + as.concat(['E']).join(', ') + ')) ' + FAIL + '\n';
      }
      const rb = RBf(k);
      if (rb) return TICK + '\n{ const m = E.trail.length; if (!' + rb + '([' + as.join(', ') + '], E)) { E.undo(m); ' + FAIL + ' } }\n';
      return 'throw new Error(' + JSON.stringify('Detlog engine: unknown procedure ' + k) + ');\n';
    }
    let curPred = '';
    for (const [k, cls] of prog.preds) {
      curPred = k.slice(0, k.lastIndexOf('/'));
      const n = arityOf(k), A = []; for (let i = 0; i < n; i++) A.push('a' + i);
      const sig = A.concat(['E']).join(', ');
      const sh = loopShape(k, cls);
      if (sh && fname.has(sh.callKey)) {
        const cf = fname.get(sh.callKey);
        out.push('function ' + fname.get(k) + '(' + sig + ') {\n' + TICK +
          '\nconst items = LA(a0); if (!items) return false; const res = [];\nfor (let i = 0; i < items.length; i++) {\nE.steps += 2; if (E.steps > E.stepLimit) OVER(E);\nconst Ov = V(null);\nif (!' + cf + '(items[i], Ov, E)) return false;\nconst o1 = LA(Ov); E.steps += (o1.length || 1); if (E.steps > E.stepLimit) OVER(E);\n' +
          (sh.cutVariant ? 'let hc = false; for (const x of o1) { res.push(x); const xd = D(x); if (xd.t === "a" && xd.n === "cut") hc = true; }\nif (hc) { const it = D(items[i]); if (it.t === "c" && it.f === "e") break; }\n' : 'for (let j = 0; j < o1.length; j++) res.push(o1[j]);\n') +
          '}\nreturn E.unify(a1, LIST(res));\n}');
        continue;
      }
      const clauseFns = cls.map((cl, ci) => genClause(cl, ci, A));
      const nm = fname.get(k);
      if (cls.length === 1) { out.push('function ' + nm + '(' + sig + ') {\n' + TICK + '\n' + clauseFns[0].inline + '\n}'); continue; }
      // clause selection by first argument, as in compilePred: variable -> all clauses; otherwise the clauses
      // whose first head argument is a variable or has the argument's key, in order
      clauseFns.forEach((c, i) => out.push('function ' + nm + '_' + i + '(' + sig + ') {\n' + c.fn + '\n}'));
      const calls = i => '{ const r = ' + nm + '_' + i + '(' + sig + '); if (r !== undefined) return r; }';
      let body = TICK + '\n';
      if (!n || cls.length === 0) body += cls.map((_, i) => calls(i)).join('\n') + '\nreturn false;';
      else {
        const tests = cls.map(cl => keyTest(D(D(cl.head).a[0]), 't0'));
        body += 'const t0 = D(a0);\nif (t0.t === "v") {\nif (E.violations.length < 1000) E.violations.push(' + JSON.stringify(k) + ');\n' + cls.map((_, i) => calls(i)).join('\n') + '\nreturn false;\n}\n';
        body += tests.map((t, i) => 'const k' + i + ' = ' + t + ';').join('\n') + '\n';
        body += 'if ((' + tests.map((_, i) => '(k' + i + ' ? 1 : 0)').join(' + ') + ') > 1 && E.violations.length < 1000) E.violations.push(' + JSON.stringify(k) + ');\n';
        body += cls.map((_, i) => 'if (k' + i + ') ' + calls(i)).join('\n') + '\nreturn false;';
      }
      out.push('function ' + nm + '(' + sig + ') {\n' + body + '\n}');
    }
    // ---------------- native tier: DET predicates in functional mode ----------------
    // A deterministic-mode predicate p__d(X1..Xn, S) entered from packet code with ground inputs ('i') and
    // fresh, distinct output variables ('o') is compiled, for that mode, to a JS function of its inputs that
    // returns its outputs (or NO / MAYBE): ground terms in and out, no logic variables, no trail, native
    // integer arithmetic, direct calls between native functions.  Anything the analysis cannot follow means
    // "no native function for this mode"; anything unexpected at run time (a non-integer in arithmetic, a
    // zero divisor, a deep stack) throws BAIL and the generic p__d runs from the untouched arguments, so
    // answers and errors are the generic code's.  Pure code: running it twice cannot be observed.
    const NAT = { fns: Object.create(null), done: new Map(), seq: 0, entry: new Map() };
    // the JavaScript emitter for the shared native compiler (src/native.js)
    const EMJS = {
      YES: 'H.YES', NO: 'H.NO', MAYBE: 'H.MAYBE', EQOP: '===', NEOP: '!==', BAIL: 'throw H.BAIL;',
      v: name => name,
      num: v => String(v),
      k: t => { if (t.t === 'c') markGround(t); return K(t); },
      box: e => 'H.INT(' + e + ')',
      unbox: e => 'H.IV(' + e + ')',
      cmp: (f, args) => '{t: "c", f: ' + JSON.stringify(f) + ', a: [' + args.join(', ') + '], gr: true}',
      eq: (a, b) => 'H.EQ(' + a + ', ' + b + ')',
      isIntVal: (e, v) => 'H.ISV(' + e + ', ' + v + ')',
      tmp: (t, e) => 'const ' + t + ' = ' + e + ';',
      isCmp: (t, f, n) => t + '.t === "c" && ' + t + '.f === ' + JSON.stringify(f) + ' && ' + t + '.a.length === ' + n,
      arg: (t, i) => t + '.a[' + i + ']',
      keyTest: (pat, t) => pat.t === 'a' ? t + ' === ' + K(pat) : keyTest(pat, t),
      fn: (name, args) => name === 'MIN' ? 'Math.min(' + args.join(', ') + ')' : name === 'MAX' ? 'Math.max(' + args.join(', ') + ')' : name === 'ABS' ? 'Math.abs(' + args[0] + ')' : 'H.' + name + '(' + args.join(', ') + ')',
      assign: (lhs, rhs) => lhs + ' = ' + rhs + ';\n',
      fail: L => 'break ' + L + ';',
      blockNoThen: (L, rc, re) => L + ': {\n' + rc + '}\n' + re,
      block: (L, ok, rc, rt, re) => '{ let ' + ok + ' = false;\n' + L + ': {\n' + rc + ok + ' = true;\n}\nif (' + ok + ') {\n' + rt + '} else {\n' + re + '}\n}\n',
      retOuts: vals => vals.length === 1 ? 'return ' + vals[0] + ';' : vals.map((v, i) => 'H.OUTS[' + i + '] = ' + v + ';').join(' ') + ' return H.YES;',
      retStatus: v => 'return ' + v + ';',
      call: (callee, ins, outs, retInt, rs, memo) => {
        const assign = outs.length === 1 ? outs[0] + ' = r;' : outs.map((o, i) => o + ' = H.OUTS[' + i + '];').join(' ');
        const get = memo
          ? 'const kk = H.KEY(' + ins.join(', ') + '); const T = H.TAB(' + JSON.stringify(memo.table) + '); let r = T.get(kk); if (r === undefined) { r = ' + callee + '(' + ins.join(', ') + '); T.set(kk, r); }\n'
          : 'const r = ' + callee + '(' + ins.join(', ') + ');\n';
        return '{ ' + get + 'if (r === H.NO || r === H.MAYBE) ' + rs + ' = r; else { ' + assign + ' ' + rs + ' = H.YES; } }\n';
      },
      func: (name, params, nOuts, selfInt, used, statusLocals, body) => {
        const names = [...new Set(used.map(u => u.name))];
        return 'function ' + name + '(' + params.map(p => p.name).join(', ') + ') {\nif (++H.N.s > H.N.l) H.OVER();\n' +
          (names.length ? 'let ' + names.join(', ') + ';\n' : '') + (statusLocals.length ? 'let ' + statusLocals.join(', ') + ';\n' : '') + body + 'throw H.BAIL;\n}';
      },
    };
    function nativeFor(k, mode) {
      const key = k + '|' + mode;
      if (NAT.done.has(key)) return NAT.done.get(key);
      const doneView = { has: k2 => NAT.done.has(k2), get: k2 => { const f = NAT.done.get(k2); return f ? { ref: 'NF.' + f.nativeName, retInt: f.retInt } : null; } };
      const batch = P.nativeBatch(prog, k, mode, EMJS, doneView, () => 'n' + (NAT.seq++));
      if (!batch) { NAT.done.set(key, null); return null; }
      const names = [...batch.values()].map(e => e.name);
      const src = '"use strict";\n' + [...batch.values()].map(e => e.src).join('\n') + '\nreturn {' + names.map(n => n + ': ' + n).join(', ') + '};';
      const made = new Function('K', 'NF', 'H', src)(consts, NAT.fns, NH);
      for (const [key2, e] of batch) { const f = made[e.name]; f.nativeName = e.name; f.retInt = e.retInt; NAT.fns[e.name] = f; NAT.done.set(key2, f); }
      return NAT.done.get(key);
    }
    // run-time entry from packet code: decide the mode, run the native function, bind the outputs
    const NH = {
      YES: { native: 'yes' }, NO: { native: 'no' }, MAYBE: { native: 'maybe' }, BAIL: { native: 'bail' }, OUTS: [], N: { s: 0, l: 0 },
      // checked (P.DETLOG_CHECKED): a non-integer, a result beyond the safe integers or a zero divisor bails
      // out to the generic code. Unchecked (the default): the type contract is assumed and nothing is tested.
      ...(P.DETLOG_CHECKED ? {
        IV: x => (x.t === 'n' && !x.f && typeof x.v === 'number') ? x.v : bailN(),
        // + - * on raw integers: a result beyond the safe integers bails to the generic code (unbounded integers)
        IADD: (a, b) => { const r = a + b; return Number.isSafeInteger(r) ? r : bailN(); },
        ISUB: (a, b) => { const r = a - b; return Number.isSafeInteger(r) ? r : bailN(); },
        IMUL: (a, b) => { const r = a * b; return Number.isSafeInteger(r) ? r : bailN(); },
        IDIV: (a, b) => b === 0 ? bailN() : Math.trunc(a / b),
        IMOD: (a, b) => { if (b === 0) return bailN(); const m = a % b; return m !== 0 && (m < 0) !== (b < 0) ? m + b : m; },
        IREM: (a, b) => b === 0 ? bailN() : a % b,
      } : {
        IV: x => x.v,
        IADD: (a, b) => a + b, ISUB: (a, b) => a - b, IMUL: (a, b) => a * b,
        IDIV: (a, b) => Math.trunc(a / b),
        IMOD: (a, b) => { const m = a % b; return m !== 0 && (m < 0) !== (b < 0) ? m + b : m; },
        IREM: (a, b) => a % b,
      }),
      INT: v => ({ t: 'n', v, f: false }),
      ISV: (x, v) => x.t === 'n' && !x.f && x.v === v,
      // a native integer result boxed as a term: a safe integer always (the operations bail otherwise)
      EQ: eqG, OVER: () => { throw new P.LimitError('step limit exceeded'); },
      // tables for memoised native calls: one per callee and mode, emptied at each entry from packet code
      T: new Map(),
      TAB: k => { let t = NH.T.get(k); if (!t) { t = new Map(); NH.T.set(k, t); } return t; },
      KEY: function () { if (arguments.length === 1) { const x = arguments[0]; if (typeof x === 'number') return x; if (x.t === 'n' && !x.f) return x.v; } let s = ''; for (let i = 0; i < arguments.length; i++) { const x = arguments[i]; s += (typeof x === 'number' ? 'i' + x : P.variantKey(x)) + '\u0001'; } return s; },
    };
    function bailN() { throw NH.BAIL; }
    // every permutation of xs, as a list, in permutation/2's order; ground lists are marked ground
    function perms(xs, fn) {
      const n = xs.length, ground = xs.every(x => { x = D(x); return x.t !== 'v' && (x.t !== 'c' || x.gr === true); });
      const cur = new Array(n), used = new Array(n).fill(false);
      const xr = xs.map(D);
      (function rec(k) {
        if (k === n) { let l = P.NIL; for (let i = n - 1; i >= 0; i--) l = ground ? { t: 'c', f: '.', a: [cur[i], l], gr: true } : { t: 'c', f: '.', a: [cur[i], l] }; fn(l); return; }
        // the builtin removes the chosen element and permutes the rest in their original order
        for (let i = 0; i < n; i++) if (!used[i]) { used[i] = true; cur[k] = xr[i]; rec(k + 1); used[i] = false; }
      })(0);
    }
    // permutation/2 under a pairwise test (src/algebra.js): a prefix whose newest element fails the test
    // against an earlier one is not extended; the permutations kept are those perms keeps, in its order
    function permsPW(xs, test, c0, fn) {
      const n = xs.length, xr = xs.map(D);
      const val = xr.map(x => (x.t === 'n' && !x.f && Number.isSafeInteger(x.v) ? x.v : null));
      if (val.includes(null)) return perms(xs, fn);
      const cur = new Array(n), pl = new Array(n), used = new Array(n).fill(false);
      (function rec(k) {
        if (k === n) { let l = P.NIL; for (let i = n - 1; i >= 0; i--) l = { t: 'c', f: '.', a: [cur[i], l], gr: true }; fn(l); return; }
        for (let i = 0; i < n; i++) if (!used[i]) {
          const y = val[i]; let ok = true;
          for (let j = k - 1; j >= 0; j--) if (!test(pl[j], y, c0 + (k - 1 - j))) { ok = false; break; }
          if (!ok) continue;
          used[i] = true; cur[k] = xr[i]; pl[k] = y; rec(k + 1); used[i] = false;
        }
      })(0);
    }
    function eqG(a, b) {
      if (a === b) return true;
      if (a.t !== b.t) return false;
      if (a.t === 'n') return a.v === b.v && a.f === b.f;
      if (a.t === 's') return a.v === b.v;
      if (a.t !== 'c' || a.f !== b.f || a.a.length !== b.a.length) return false;
      for (let i = 0; i < a.a.length; i++) if (!eqG(a.a[i], b.a[i])) return false;
      return true;
    }
    const ATOMS = { yes: P.Atom('yes'), no: P.Atom('no') };
    // returns true when the native function answered (outputs and status bound), undefined otherwise
    function natEntry(k, args, E) {
      if (!P.DETLOG_NATIVE) return undefined;
      const n = args.length - 1; let mode = ''; const ins = [], outv = [];
      for (let i = 0; i < n; i++) {
        const x = D(args[i]);
        if (x.t === 'v') { if (outv.includes(x)) return undefined; mode += 'o'; outv.push(x); continue; }
        if (x.t === 'n' && !x.f && typeof x.v === 'number') { mode += 'n'; ins.push(x.v); continue; }
        const r = P.resolve(x);
        if (r.t === 'c' && !r.gr) return undefined;
        mode += 'i'; ins.push(r);
      }
      const S = D(args[n]); if (S.t !== 'v' || outv.includes(S)) return undefined;
      // per predicate: mode -> native function (or null), without building a key per call
      let byMode = NAT.entry.get(k); if (!byMode) { byMode = new Map(); NAT.entry.set(k, byMode); }
      let fn = byMode.get(mode); if (fn === undefined) { fn = nativeFor(k, mode); byMode.set(mode, fn); }
      if (!fn) return undefined;
      let r;
      NH.N.s = E.steps; NH.N.l = E.stepLimit; if (NH.T.size) NH.T.clear();
      try { r = fn.apply(null, ins); }
      catch (e) { E.steps = NH.N.s; if (e === NH.BAIL || e instanceof RangeError || e instanceof TypeError) return undefined; throw e; }
      E.steps = NH.N.s; E.nativeCalls = (E.nativeCalls || 0) + 1;
      if (r === NH.MAYBE) return undefined;
      if (r === NH.NO) { E.bind(S, ATOMS.no); return true; }
      if (outv.length === 1) E.bind(outv[0], fn.retInt ? P.Int(r) : r); else for (let i = 0; i < outv.length; i++) E.bind(outv[i], NH.OUTS[i]);
      E.bind(S, ATOMS.yes); return true;
    }
    P.nativeFor = nativeFor;

    const src = '"use strict";\n' + out.join('\n') + '\nreturn {' + [...fname].map(([k, f]) => JSON.stringify(k) + ': ' + f).join(', ') + '};';
    const OVER = E => { throw new P.LimitError('step limit (' + E.stepLimit + ') exceeded'); };
    const BADV = { t: 'v', ref: null }; // stands for a variable that was never created (an unbound leaf)
    const fns = new Function('K', 'RB', 'D', 'V', 'LA', 'LIST', 'OVER', 'INT', 'COPY', 'BADV', 'NATE', 'PERMS', 'LIMIT', 'PERMSPW', src)(consts, rbs, D, Var, listToArray, list, OVER, P.Int, P.copy, BADV, natEntry, perms, P.LimitError, permsPW);
    const preds = new Map();
    for (const [k, f] of Object.entries(fns)) preds.set(k, { k, fn: (args, E) => f(...args, E), pos: f });
    return { preds, src, jit: true, nat: NAT };
  }

  const cache = new WeakMap();
  function compiled(prog) {
    let f = cache.get(prog);
    if (!f) {
      try { f = P.DETLOG_JIT === false ? new FastDetlog(prog) : jitCompile(prog); }
      catch (e) { f = new FastDetlog(prog); f.jitError = e.message; }
      cache.set(prog, f);
    }
    return f;
  }
  P.jitCompile = jitCompile;
  P.loopShape = loopShape;
  // the (predicate, mode) pairs the native tier compiled for a program (the C export compiles the same)
  P.nativeModesOf = prog => { const F = cache.get(prog); return F && F.nat ? [...F.nat.done].filter(([, f]) => f).map(([k]) => k) : []; };
  if (P.DETLOG_NATIVE === undefined) P.DETLOG_NATIVE = true;
  if (P.DETLOG_CHECKED === undefined) P.DETLOG_CHECKED = false; // the native tier assumes its type contract

  // same interface and result shape as runDetlog
  function runDetlogFast(prog, qpred, varNames, opts) {
    opts = opts || {};
    let F;
    try { F = compiled(prog); } catch (e) { return Object.assign(P.runDetlog(prog, qpred, varNames, opts), { engine: 'reference (compile failed: ' + e.message + ')' }); }
    const E = new P.DetEngine(prog, opts);
    const nv = varNames.length, args = new Array(nv + 1);
    for (let i = 0; i < nv; i++) args[i] = Var(varNames[i]);
    const Rv = Var('R'); args[nv] = Rv;
    const k = qpred + '__cp/' + (nv + 1);
    const t0 = P.now(); let ok = false, error = null;
    try {
      const r = F.preds.get(k); if (!r || !r.fn) throw new Error('no query predicate ' + k);
      ok = r.pos ? (args.push(E), r.pos.apply(null, args)) : r.fn(args, E);
    } catch (e) {
      if (e instanceof RangeError) return Object.assign(P.runDetlog(prog, qpred, varNames, opts), { engine: 'reference (JS stack exhausted)' });
      error = e.message;
    }
    const t1 = P.now();
    // noDecode: the answers are not formatted as text (to time the computation alone)
    if (opts.noDecode) return { ok, error, steps: E.steps, timeMs: t1 - t0 };
    const res = P.decodePacket(ok, error, Rv, varNames);
    return { ok: res.ok, answers: res.answers, events: res.events, output: res.output, error: res.error,
      engine: F.jit ? 'fast (JIT)' : 'fast', steps: E.steps, decisions: E.decisions, violations: E.violations.length,
      violationPreds: E.violations.length ? [...new Set(E.violations)] : [], cps: 0, maxCP: 0, timeMs: t1 - t0,
      memoHits: E.memoHits, memoStores: E.memoStores, rowsBuilt: E.rowsBuilt, maxRows: E.maxRows };
  }
  // Calls a compiled Detlog predicate (key, e.g. 'app__cp/4') with the given arguments; the last
  // is the answer packet. For the interpreter's per-call routes (src/interp.js).
  function detlogCall(prog, key, args, opts) {
    const F = compiled(prog);
    const r = F.preds.get(key); if (!r || !r.fn) return null;
    const E = new P.DetEngine(prog, opts || {});
    const ok = r.pos ? r.pos.apply(null, args.concat([E])) : r.fn(args, E);
    return { ok, steps: E.steps };
  }
  P.detlogCall = detlogCall;
  P.FastDetlog = FastDetlog; P.runDetlogFast = runDetlogFast;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog Detlog interpreter: the choicepointless, cutless interpreter of detlog2 (part 1).
   It runs the cut-free program (rule CUT applied, higher-order calls specialised) as answer packets:
   - a predicate call computes the callee's packet (its answers and output, in Prolog order) and splices
     it into the conjunction: one row at a time, bindings undone between rows - no choicepoint is ever
     created, so there is no choicepoint stack and nothing to backtrack into;
   - clauses are compiled once into closures, and heads are matched WAM-style without copying;
   - commitment ((C -> T ; E), \+, once) takes the first row of C and never demands the rest;
   - a cut inside a branch (a cut marker in the converted code) is a status that stops the remaining
     rows and clauses of its clause's predicate.
   Its answers are checked against Prolog and against the converted Detlog code by the proof checker. */
(function (P) {
  'use strict';
  const { Var, Cmp, NIL, list, deref, listToArray, termVars, Int, Str, Atom } = P;
  const D = deref;
  const OK = 0, STOP = 1, CUT = 2;

  function Machine(opts) {
    opts = opts || {};
    this.trail = []; this.steps = 0; this.stepLimit = opts.stepLimit || 5e7; this.items = null; this.calls = 0; this.rows = 0; this.globals = new Map(); this.out = '';
  }
  Machine.prototype.bind = function (v, t) { v.ref = t; this.trail.push(v); };
  Machine.prototype.undo = function (m) { const tr = this.trail; while (tr.length > m) tr.pop().ref = null; };
  Machine.prototype.mark = function () { return this.trail.length; }; // every binding is trailed here
  Machine.prototype.unify = P.Engine.prototype.unify;
  Machine.prototype.tick = function (n) { this.steps += n || 1; if (this.steps > this.stepLimit) throw new P.LimitError('step limit (' + this.stepLimit + ') exceeded'); };
  // output goes into the packet being built, in the order it is written
  Machine.prototype.write = function (s) { if (!s) return; const it = this.items; const l = it[it.length - 1]; if (l && l.out !== undefined) l.out += s; else it.push({ out: s }); };

  function Interp(conv) {
    this.ir = conv.ir; this.preds = new Map(); this.prog = conv.prog;
    for (const [k, p] of conv.ir) this.ref(k).p = p;
    for (const [k, p] of conv.ir) this.ref(k).fn = this.compilePred(k, p);
  }
  Interp.prototype.ref = function (k) { let r = this.preds.get(k); if (!r) { r = { k, fn: null }; this.preds.set(k, r); } return r; };

  // packet of k(args): array of {row: [instances of args]} and {out: text}
  Interp.prototype.compilePred = function (k, p) {
    if (p.error) return () => { throw new Error('not converted: ' + k + ': ' + p.error); };
    const cc = p.clauses.map(cl => this.compileClause(cl));
    const n = +k.slice(k.lastIndexOf('/') + 1);
    const keyOf = t => { t = D(t); return t.t === 'c' ? 'c' + t.f + '/' + t.a.length : t.t === 'a' ? 'a' + t.n : t.t === 'n' ? 'n' + t.v + (t.f ? 'f' : '') : t.t === 's' ? 's' + t.v : null; };
    const heads = p.clauses.map(cl => n ? keyOf(D(cl.head).a[0]) : null);
    const index = new Map(); const varIdx = [];
    heads.forEach((h, i) => { if (h === null) varIdx.push(i); });
    for (const h of new Set(heads.filter(x => x !== null))) index.set(h, heads.map((x, i) => (x === h || x === null) ? i : -1).filter(i => i >= 0));
    const all = cc.map((_, i) => i);
    return function (args, M) {
      M.tick(); M.calls++;
      let cand = all;
      if (n && cc.length > 1) { const a0 = D(args[0]); if (a0.t !== 'v') cand = index.get(keyOf(a0)) || varIdx; }
      const save = M.items; const items = []; M.items = items;
      try {
        for (let j = 0; j < cand.length; j++) {
          const c = cc[cand[j]];
          const env = new Array(c.nslots); const m = M.trail.length;
          let st = OK;
          if (c.head(args, env, M)) st = c.body(env, M, () => { const row = new Array(n); for (let i = 0; i < n; i++) row[i] = P.resolve(args[i]); items.push({ row }); M.rows++; return OK; });
          M.undo(m);
          if (st === CUT) break; // a cut stops the remaining clauses
        }
      } finally { M.items = save; }
      return items;
    };
  };
  Interp.prototype.compileClause = function (cl) {
    const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
    const vars = termVars(Cmp('-', [cl.head, cl.body]));
    const slot = new Map(); vars.forEach((v, i) => slot.set(v, i));
    const seen = new Set();
    const ms = hargs.map(h => P.FastDetlog.prototype.compileMatch.call(this, h, slot, seen));
    const nh = ms.length;
    return { nslots: vars.length, head: nh ? (args, env, M) => { for (let i = 0; i < nh; i++) if (!ms[i](args[i], env, M)) return false; return true; } : () => true, body: this.compileGoal(cl.body, slot) };
  };
  Interp.prototype.compileBuild = P.FastDetlog.prototype.compileBuild;
  Interp.prototype.compileMatch = P.FastDetlog.prototype.compileMatch;

  // a goal is compiled to g(env, M, k): it calls k() once per answer (bindings in place) and returns
  // OK, or STOP (a consumer wants no more answers), or CUT (a cut was reached: drop the remaining alternatives)
  Interp.prototype.compileGoal = function (g, slot) {
    g = D(g); const k = P.key(g);
    const self = this;
    switch (k) {
      case ',/2': {
        // runs of deterministic goals become one in-place test (no continuation closures)
        const flat = P.flatConj(g); const parts = [];
        for (let i = 0; i < flat.length;) {
          if (this.isDet(flat[i])) { let j = i; while (j < flat.length && this.isDet(flat[j])) j++; parts.push({ test: this.compileTest(flat.slice(i, j), slot) }); i = j; }
          else { parts.push({ goal: this.compileGoal(flat[i], slot) }); i++; }
        }
        let c = null;
        for (let i = parts.length - 1; i >= 0; i--) {
          const p = parts[i], next = c;
          if (p.test) {
            const t = p.test;
            c = next ? (env, M, kk) => { const m = M.trail.length; if (!t(env, M)) { M.undo(m); return OK; } const s = next(env, M, kk); M.undo(m); return s; }
                     : (env, M, kk) => { const m = M.trail.length; if (!t(env, M)) { M.undo(m); return OK; } const s = kk(); M.undo(m); return s; };
          } else {
            const gi = p.goal;
            c = next ? (env, M, kk) => gi(env, M, () => next(env, M, kk)) : gi;
          }
        }
        return c;
      }
      case 'true/0': return (env, M, kk) => { M.tick(); return kk(); };
      case 'fail/0': case 'false/0': return (env, M) => { M.tick(); return OK; };
      case '!/0': return (env, M, kk) => { M.tick(); const s = kk(); return s === STOP ? STOP : CUT; };
      case ';/2': {
        const l = D(g.a[0]);
        if (l.t === 'c' && l.f === '->' && l.a.length === 2) return this.ite(l.a[0], l.a[1], g.a[1], slot);
        const A = this.compileGoal(g.a[0], slot), B = this.compileGoal(g.a[1], slot);
        return (env, M, kk) => { M.tick(); const s = A(env, M, kk); if (s !== OK) return s; return B(env, M, kk); };
      }
      case '->/2': return this.ite(g.a[0], g.a[1], P.FAIL, slot);
      case '\\+/1': {
        if (P.flatConj(g.a[0]).every(x => this.isDet(x))) {
          const t = this.compileTest(P.flatConj(g.a[0]), slot);
          return (env, M, kk) => { M.tick(); const m = M.trail.length; const r = t(env, M); M.undo(m); return r ? OK : kk(); };
        }
        const G = this.compileGoal(g.a[0], slot);
        return (env, M, kk) => { M.tick(); let found = false; const m = M.trail.length; G(env, M, () => { found = true; return STOP; }); M.undo(m); return found ? OK : kk(); };
      }
      case 'findall/3': {
        const T = this.compileBuild(g.a[0], slot), G = this.compileGoal(g.a[1], slot), L = this.compileBuild(g.a[2], slot);
        return (env, M, kk) => {
          M.tick(); const res = []; const m = M.trail.length;
          G(env, M, () => { res.push(P.resolve(T(env))); return OK; });
          M.undo(m);
          const m2 = M.trail.length;
          if (!M.unify(L(env), list(res))) { M.undo(m2); return OK; }
          const s = kk(); M.undo(m2); return s;
        };
      }
      case 'aggregate_all/3': {
        const spec = D(g.a[0]); const sp = spec.t === 'a' ? spec.n : spec.f;
        const T = spec.t === 'c' ? this.compileBuild(spec.a[0], slot) : () => P.TRUE;
        const G = this.compileGoal(g.a[1], slot), R = this.compileBuild(g.a[2], slot);
        return (env, M, kk) => {
          M.tick(); const res = []; const m = M.trail.length;
          G(env, M, () => { res.push(P.resolve(T(env))); return OK; });
          M.undo(m);
          const v = aggregate(sp, res); if (v === null) return OK;
          const m2 = M.trail.length;
          if (!M.unify(R(env), v)) { M.undo(m2); return OK; }
          const s = kk(); M.undo(m2); return s;
        };
      }
    }
    const as = g.t === 'c' ? g.a.map(x => this.compileBuild(x, slot)) : []; const n = as.length;
    const build = env => { const a = new Array(n); for (let i = 0; i < n; i++) a[i] = as[i](env); return a; };
    if (this.ir.has(k)) {
      // splice the callee's packet into the conjunction
      const r = this.ref(k);
      return (env, M, kk) => {
        const args = build(env);
        const pk = r.fn(args, M);
        for (let i = 0; i < pk.length; i++) {
          const it = pk[i];
          if (it.out !== undefined) { M.write(it.out); continue; }
          M.tick();
          const m = M.trail.length; const row = it.row; let ok = true;
          for (let j = 0; j < n; j++) if (!M.unify(args[j], row[j])) { ok = false; break; }
          if (ok) { const s = kk(); M.undo(m); if (s !== OK) return s; } else M.undo(m);
        }
        return OK;
      };
    }
    if (k === '=/2') { const a = as[0], b = as[1]; return (env, M, kk) => { M.tick(); const m = M.trail.length; if (!M.unify(a(env), b(env))) { M.undo(m); return OK; } const s = kk(); M.undo(m); return s; }; }
    const bi = P.builtins[k];
    if (bi && bi.nondet) {
      return (env, M, kk) => {
        M.tick(); const a = build(env); const m = M.trail.length; const it = bi.fn(a, M, null);
        for (;;) {
          const r = it.next(); if (r.done) break;
          M.tick();
          const s = kk();
          if (s !== OK) { M.undo(m); return s; }
          if (r.value === 'last') break;
        }
        M.undo(m); return OK;
      };
    }
    if (bi && bi.call) {
      // higher-order builtins that the converter did not specialise (maplist on a variable closure, phrase, ...)
      return (env, M, kk) => { M.tick(); const ng = bi.fn(build(env), M, null); if (ng === null) return OK; return self.dynamicGoal(ng, M, kk); };
    }
    if (bi) return (env, M, kk) => { M.tick(); const a = build(env); const m = M.trail.length; if (!bi.fn(a, M, null)) { M.undo(m); return OK; } const s = kk(); M.undo(m); return s; };
    return () => { throw new Error('Detlog interpreter: unknown procedure ' + k); };
  };
  // deterministic goals: builtins that are neither nondeterministic nor higher-order (their packet has at most one row)
  Interp.prototype.isDet = function (g) {
    g = D(g); const k = P.key(g);
    if (k === 'true/0' || k === 'fail/0' || k === 'false/0' || k === '=/2') return true;
    if (!k || this.ir.has(k)) return false;
    const b = P.builtins[k]; return !!(b && !b.nondet && !b.call);
  };
  // a run of deterministic goals as one boolean test; bindings stay in place (the caller undoes them)
  Interp.prototype.compileTest = function (gs, slot) {
    const ts = gs.map(g => {
      g = D(g); const k = P.key(g);
      if (k === 'true/0') return (env, M) => { M.tick(); return true; };
      if (k === 'fail/0' || k === 'false/0') return (env, M) => { M.tick(); return false; };
      const as = g.t === 'c' ? g.a.map(x => this.compileBuild(x, slot)) : []; const n = as.length;
      if (k === '=/2') { const a = as[0], b = as[1]; return (env, M) => { M.tick(); return M.unify(a(env), b(env)); }; }
      const fn = P.builtins[k].fn;
      if (n === 2) { const a0 = as[0], a1 = as[1]; return (env, M) => { M.tick(); return fn([a0(env), a1(env)], M, null); }; }
      return (env, M) => { M.tick(); const a = new Array(n); for (let i = 0; i < n; i++) a[i] = as[i](env); return fn(a, M, null); };
    });
    if (ts.length === 1) return ts[0];
    const n = ts.length;
    return (env, M) => { for (let i = 0; i < n; i++) if (!ts[i](env, M)) return false; return true; };
  };
  Interp.prototype.ite = function (C, T, F, slot) {
    const Tg = this.compileGoal(T, slot), Fg = this.compileGoal(F, slot);
    if (P.flatConj(C).every(x => this.isDet(x))) {
      const t = this.compileTest(P.flatConj(C), slot);
      return (env, M, kk) => { M.tick(); const m = M.trail.length; if (t(env, M)) { const s = Tg(env, M, kk); M.undo(m); return s; } M.undo(m); return Fg(env, M, kk); };
    }
    const Cg = this.compileGoal(C, slot);
    return (env, M, kk) => {
      M.tick();
      let found = false, ts = OK; const m = M.trail.length;
      Cg(env, M, () => { found = true; ts = Tg(env, M, kk); return STOP; });
      M.undo(m);
      return found ? ts : Fg(env, M, kk);
    };
  };
  // a goal built at run time (rare): compiled on the fly with no clause variables
  Interp.prototype.dynamicGoal = function (g, M, kk) {
    const vars = termVars(g); const slot = new Map(); const env = vars.slice(); vars.forEach((v, i) => slot.set(v, i));
    return this.compileGoal(g, slot)(env, M, kk);
  };
  function aggregate(sp, ts) {
    switch (sp) {
      case 'count': return Int(ts.length);
      case 'sum': { let s = Int(0); for (const x of ts) s = P.evalArith(Cmp('+', [s, x])); return s; }
      case 'max': if (!ts.length) return null; return ts.map(P.evalArith).reduce((m, x) => x.v > m.v ? x : m);
      case 'min': if (!ts.length) return null; return ts.map(P.evalArith).reduce((m, x) => x.v < m.v ? x : m);
      case 'bag': return list(ts);
      case 'set': return list(P.sortUnique(ts));
    }
    throw new Error('aggregate_all: unknown spec ' + sp);
  }

  const cache = new WeakMap();
  function runDetlogInterp(conv, qpred, varNames, opts) {
    opts = opts || {};
    let I = cache.get(conv); if (!I) { I = new Interp(conv); cache.set(conv, I); }
    const M = new Machine(opts);
    const vs = varNames.map(n => Var(n)); const k = qpred + '/' + varNames.length;
    const t0 = P.now(); let items = null, error = null, limit = false;
    try { const r = I.preds.get(k); if (!r) throw new Error('no query predicate ' + k); M.items = []; items = r.fn(vs, M); }
    catch (e) {
      if (e instanceof RangeError) return Object.assign(runFallback(conv, qpred, varNames, opts), { engine: 'Detlog engine (interpreter ran out of JS stack)' });
      error = e.limit ? e.message : e.prolog ? (e.term ? P.errText(e.term) : e.message) : e.message; limit = !!e.limit;
    }
    const t1 = P.now();
    const events = [], answers = []; let output = '';
    if (items) for (const it of items) {
      if (it.out !== undefined) { output += it.out; const l = events[events.length - 1]; if (l && l.k === 'out') l.text += it.out; else events.push({ k: 'out', text: it.out }); continue; }
      const nm = P.namer(); const text = varNames.length ? varNames.map((n, i) => n + ' = ' + P.show(it.row[i], { varName: nm })).join(', ') : 'true';
      answers.push({ text }); events.push({ k: 'row', text });
    }
    return { ok: !error, answers, events, output, steps: M.steps, cps: 0, maxCP: 0, calls: M.calls, packetRows: M.rows, timeMs: t1 - t0, error, limit, engine: 'interpreter', violations: 0, violationPreds: [] };
  }
  function runFallback(conv, qpred, varNames, opts) { return P.runDetlogFast(P.loadProgram(conv.text), qpred, varNames, opts); }
  P.DetlogInterp = Interp; P.runDetlogInterp = runDetlogInterp;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog back-converter: Detlog -> Prolog.
   Works from the Detlog text alone (so edited Detlog can be back-converted): each generated template is
   recognised and turned back into the Prolog goal it computes.  Cuts are restored from the if_commit chains
   of rule CUT, specialised maplist/foldl closures are folded back, S2A loops become formulas or facts and
   memo wrappers are dropped.  Every change from the original source is reported as a warning. */
(function (P) {
  'use strict';
  const { Atom, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, listToArray, copy, termVars, show } = P;
  const D = deref;
  const conj = P.conjT;
  const isA = (t, n) => { t = D(t); return t.t === 'a' && t.n === n; };
  const isC = (t, f, n) => { t = D(t); return t.t === 'c' && t.f === f && (n === undefined || t.a.length === n); };
  const flat = g => P.flatConj(g);

  function BackError(msg) { const e = new Error(msg); e.back = true; return e; }

  function backConvert(detlogText, opts) {
    opts = opts || {};
    const prog = P.loadProgram(detlogText);
    const res = { clauses: [], warnings: [], notes: [], preds: [], queries: [], text: '' };
    const cpPreds = prog.order.filter(k => /__cp\/\d+$/.test(k));
    const specInfo = new Map(); // spec pred key -> {kind, closureClause}
    const predClauses = new Map(); // p/n -> [clause terms]
    const predNotes = new Map();
    const note = (k, m) => { if (!predNotes.has(k)) predNotes.set(k, []); if (!predNotes.get(k).includes(m)) predNotes.get(k).push(m); };
    const getCls = k => { const c = prog.preds.get(k); if (!c) throw BackError('missing Detlog predicate ' + k); return c; };

    for (const k of cpPreds) {
      const [f, nS] = splitKey(k); const n = +nS - 1; const pname = f.replace(/__cp$/, ''); const pk = pname + '/' + n;
      try {
        const clauses = decompPacketPred(k, pk);
        predClauses.set(pk, clauses);
      } catch (e) {
        if (!e.back) throw e;
        res.warnings.push({ pred: pk, kind: 'error', msg: 'not back-convertible: ' + e.message });
        predClauses.set(pk, null);
      }
    }

    // decompile the packet predicate k (p__cp/n+1) into Prolog clauses of p/n
    function decompPacketPred(k, pk) {
      const cls = getCls(k);
      if (cls.length !== 1) throw BackError(k + ' has ' + cls.length + ' clauses (expected one)');
      return decompPacketClause(cls[0], pk, P.name(cls[0].head).replace(/__cp$/, ''));
    }
    function decompPacketClause(cl, pk, pname) {
      const head = D(cl.head); const A = head.a.slice(0, -1); const Rows = head.a[head.a.length - 1];
      const gs = flat(cl.body);
      const b0 = D(gs[0]);
      // empty / dynamic
      if (gs.length === 1 && isC(b0, '=', 2) && D(b0.a[0]) === D(Rows) && isA(b0.a[1], '[]')) { note(pk, 'no clauses'); return []; }
      // unsupported
      if (isC(b0, 'detlog_unsupported', 2)) throw BackError('the predicate was not converted (' + P.textOf(b0.a[1]) + ')');
      // FACTS
      if (gs.length === 1 && isC(b0, 'cp_filter', 3)) {
        return listToArray(b0.a[0]).map(r => { const args = listToArray(D(r).a[0]); return { head: Cmp(pname, args.map(x => copy(x))), body: P.TRUE }; });
      }
      // S2A
      if (gs.length === 1 && isC(b0, 's2a_rows', 3)) { note(pk, 'S2A loop back-converted'); return s2aClauses(b0.a[0], pname, A.length, pk); }
      // DET wrapper:  copy_term(A, B), p__d(B.., S), p__dr(S, B.., A.., Rows)  -- the packet code is p__cpx
      if (gs.length === 3 && isC(b0, 'copy_term', 2) && D(gs[1]).t === 'c' && /__d$/.test(D(gs[1]).f) && D(gs[2]).t === 'c' && /__dr$/.test(D(gs[2]).f)) {
        note(pk, 'deterministic mode dropped (DET is an optimisation only)');
        const inner = getCls(pname + '__cpx/' + (A.length + 1));
        if (inner.length !== 1) throw BackError('DET packet predicate has several clauses');
        const ih = D(inner[0].head);
        return decompPacketClause({ head: Cmp(pname + '__cp', ih.a), body: inner[0].body }, pk, pname);
      }
      // MEMO wrapper
      if (gs.length === 2 && isC(b0, 'memo_lookup', 3)) {
        note(pk, 'memo table dropped (memoisation is an optimisation only)');
        const mk = P.key(gs[1]); const mcls = getCls(mk);
        const none = mcls.find(c => isA(D(c.head).a[0], 'none'));
        if (!none) throw BackError('memo wrapper without a none clause');
        const call = D(flat(none.body)[0]);
        const inner = getCls(P.key(call));
        if (inner.length !== 1) throw BackError('memo compute predicate has several clauses');
        return decompPacketClause(inner[0], pk, pname);
      }
      // PRED: clause packets then rows_concat
      const last = D(gs[gs.length - 1]);
      if ((isC(last, 'rows_concat', 2) || isC(last, 'rows_cut_concat', 2)) && D(last.a[1]) === D(Rows) && gs.length >= 2 && !isC(b0, 'copy_term', 2) && !isC(b0, 'if_commit', 3)) {
        const out = [];
        for (const g of gs.slice(0, -1)) {
          const cc = getCls(P.key(g)); if (cc.length !== 1) throw BackError('clause packet ' + P.key(g) + ' has several clauses');
          out.push(...decompClausePacket(cc[0], pname, pk));
        }
        return out;
      }
      // CLAUSE (single clause)
      return decompClausePacket(cl, pname, pk);
    }
    function s2aClauses(spec, pname, n, pk) {
      spec = D(spec); const K = D(spec.a[0]).v; const cols = listToArray(spec.a[1]).map(D);
      const allFormula = cols.every(c => c.f === 'newton' || c.f === 'const') && cols.some(c => c.f === 'newton');
      if (allFormula && K > 3) {
        const isId = c => c.f === 'newton' && listToArray(c.a[0]).map(x => D(x).v).join(',') === '0,1';
        const idj = cols.findIndex(isId);
        const I = idj >= 0 ? Var('A' + (idj + 1)) : Var('I'); const As = []; const goals = [Cmp('between', [Int(0), Int(K - 1), I])];
        cols.forEach((c, j) => {
          if (j === idj) { As.push(I); return; }
          const Aj = Var('A' + (j + 1)); As.push(Aj);
          if (c.f === 'const') goals.push(Cmp('=', [Aj, c.a[0]]));
          else goals.push(Cmp('is', [Aj, newtonExpr(listToArray(c.a[0]).map(x => D(x).v), I)]));
        });
        note(pk, 'S2A loop written as a formula over I = 0..' + (K - 1));
        return [{ head: Cmp(pname, As), body: conj(goals) }];
      }
      const out = [];
      for (let I = 0; I < K; I++) {
        const row = cols.map(c => c.f === 'const' ? c.a[0] : c.f === 'data' ? listToArray(c.a[0])[I] : Int(listToArray(c.a[0]).map(x => D(x).v).reduce((s, d, i) => s + d * P.binom(I, i), 0)));
        out.push({ head: Cmp(pname, row.map(x => copy(x))), body: P.TRUE });
      }
      note(pk, 'S2A loop written as its ' + K + ' facts (the original rules are replaced by their answer table)');
      return out;
    }
    function newtonExpr(ds, I) {
      const { c, den } = P.newtonPoly(ds);
      const mon = k => k === 1 ? I : k === 2 ? Cmp('*', [I, I]) : Cmp('*', [Cmp('*', [I, I]), I]);
      let e = null;
      for (let k = 3; k >= 0; k--) {
        if (!c[k]) continue;
        const a = Math.abs(c[k]);
        const t = k === 0 ? Int(a) : a === 1 ? mon(k) : Cmp('*', [Int(a), mon(k)]);
        if (e === null) e = c[k] < 0 ? (k === 0 ? Int(-a) : Cmp('-', [t])) : t;
        else e = Cmp(c[k] < 0 ? '-' : '+', [e, t]);
      }
      if (e === null) e = Int(0);
      return den === 1 ? e : Cmp('//', [e, Int(den)]);
    }
    // clause packet:  if_commit(copy_term(A, H), (Code, project_rows(R0, L, H, Rows)), Rows = [])
    //            or:  copy_term(A, H), Code, project_rows(R0, L, H, Rows)   (head arguments distinct variables)
    function decompClausePacket(cl, pname, pk) {
      const gs = flat(cl.body);
      let ren0, tg;
      // call-through:  h__cp(A.., Rows) :- q__cp(A.., Rows)
      { const h = D(cl.head); const g0 = D(gs[0]);
        if (gs.length === 1 && g0.t === 'c' && /__cp$/.test(g0.f) && g0.a.length === h.a.length && g0.a.every((x, i) => D(x) === D(h.a[i]))) {
          const vs = h.a.slice(0, -1).map((_, i) => Var('X' + (i + 1)));
          return [{ head: Cmp(pname, vs), body: Cmp(g0.f.replace(/__cp$/, ''), vs) }];
        } }
      if (gs.length === 1 && isC(gs[0], 'if_commit', 3) && isC(D(gs[0]).a[0], 'copy_term', 2)) { ren0 = D(D(gs[0]).a[0]); tg = flat(D(gs[0]).a[1]); }
      else if (gs.length >= 2 && isC(gs[0], 'copy_term', 2)) { ren0 = D(gs[0]); tg = gs.slice(1); }
      else throw BackError('unexpected clause packet ' + P.key(cl.head));
      const H = listToArray(ren0.a[1]);
      if (isC(tg[tg.length - 1], 'strip_cut', 2)) tg = tg.slice(0, -1);
      const pr = D(tg[tg.length - 1]);
      let R0, L, code;
      if (isC(pr, 'project_rows', 4)) { R0 = D(pr.a[0]); L = pr.a[1]; code = tg.slice(0, -1); }
      else { // identity projection: the environment is the head arguments and the code computes the packet itself
        const Rows = D(cl.head).a[D(cl.head).a.length - 1];
        if (!H.every(x => D(x).t === 'v')) throw BackError('clause packet without project_rows');
        R0 = D(Rows); L = list(H); code = tg;
      }
      const names = new Map();
      const ctx = { names, L, pk };
      const body = decompCode(code, R0, ctx);
      let clause = { head: Cmp(pname, H.map(x => ren(x, names))), body };
      const restored = restoreCuts(clause, pname, pk);
      return restored.map(c => cleanup(c, pk));
    }
    function ren(t, names) {
      t = D(t);
      if (t.t === 'v') {
        if (!t.name || t.name === '_') return Var('_');
        let v = names.get(t.name); if (!v) { v = Var(t.name); names.set(t.name, v); } return v;
      }
      if (t.t === 'c') return Cmp(t.f, t.a.map(x => ren(x, names)));
      return t;
    }

    // decompile a Detlog code sequence that computes packet O (in env L) into one Prolog goal
    function decompCode(gs, O, ctx) {
      gs = gs.map(D);
      if (!gs.length) throw BackError('empty code');
      const u = unit(gs, 0, ctx);
      let goal = u.goal; let i = u.next; let cur = u.out;
      while (i < gs.length) {
        const g = gs[i];
        // seq: nm(Cur, Next)
        if (g.t === 'c' && g.a.length === 2 && D(g.a[0]) === cur && isSeqAux(P.key(g))) {
          const rest = decompSeqAux(P.key(g), ctx);
          goal = conj([goal, rest]); cur = D(g.a[1]); i++; continue;
        }
        if (isC(g, '=', 2) && D(g.a[1]) === cur) { cur = D(g.a[0]); i++; continue; }
        throw BackError('unexpected goal ' + show(g, { varName: v => v.name || '_' }));
      }
      if (cur !== D(O)) throw BackError('code does not compute its output packet');
      return goal;
    }
    function isSeqAux(k) {
      const cls = prog.preds.get(k); if (!cls || cls.length !== 2) return false;
      return isA(D(cls[0].head).a[0], '[]');
    }
    function decompSeqAux(k, ctx) {
      const cls = getCls(k);
      const rk = P.key(flat(cls[1].body)[0]);
      const rcls = getCls(rk);
      const ecl = rcls.find(c => isC(D(c.head).a[0], 'e', 1));
      if (!ecl) throw BackError('row predicate ' + rk + ' without an e/1 clause');
      const gs = flat(ecl.body);
      if (!isC(gs[0], 'copy_term', 2)) throw BackError('row predicate without copy_term');
      return decompCode(gs.slice(1), D(ecl.head).a[1], ctx);
    }
    function auxBody(k, which, ctx) { // single-clause aux nm(e(L), O) :- Code
      const cls = getCls(k);
      const cl = which ? cls.find(which) : cls[0];
      if (!cl) throw BackError('missing clause of ' + k);
      const h = D(cl.head);
      return decompCode(flat(cl.body), h.a[h.a.length - 1], ctx);
    }

    // one unit: returns {goal, out, next}
    function unit(gs, i, ctx) {
      const g = gs[i]; const k = P.key(g);
      const r = x => ren(x, ctx.names);
      // O = [e(L)] / O = []
      if (isC(g, '=', 2)) {
        const rhs = D(g.a[1]);
        if (isA(rhs, '[]')) return { goal: P.FAIL, out: D(g.a[0]), next: i + 1 };
        const l = listToArray(rhs);
        if (l && l.length === 1 && isC(l[0], 'e', 1)) return { goal: P.TRUE, out: D(g.a[0]), next: i + 1 };
        if (l && l.length === 2 && isA(l[0], 'cut') && isC(l[1], 'e', 1)) return { goal: Atom('!'), out: D(g.a[0]), next: i + 1 };
        if (l && l.length === 2 && isC(l[0], 'out', 1)) throw BackError('out item without effect_text');
      }
      if (k === 'if_commit/3') {
        const C = D(g.a[0]), T = flat(g.a[1]), F = flat(g.a[2]);
        // det:  if_commit(B, O = [e(L)], O = [])
        const OT = outOfSimple(T), OF = outOfSimple(F);
        if (OT && OF && OT.v === OF.v && OT.kind === 'row' && OF.kind === 'none') return { goal: r(C), out: OT.v, next: i + 1 };
        // DET-call:  if_commit((q__d(As.., S), S \== maybe), if_commit(S = yes, ..), (q__cp(As.., P), splice_extend(..)))
        if (isC(C, ',', 2) && D(D(C).a[0]).t === 'c' && /__d$/.test(D(D(C).a[0]).f) && isC(D(C).a[1], '\\==', 2)) {
          const Os = findOut(F);
          return { goal: decompCode(F, Os, ctx), out: Os, next: i + 1 };
        }
        // splice:  if_commit(splice_safe(..), Chain, Seq)
        if (isC(C, 'splice_safe', 2)) {
          ctx.splice = true; note(ctx.pk, 'splice written back as the sequential conjunction');
          const Os = findOut(F);
          return { goal: decompCode(F, Os, ctx), out: Os, next: i + 1 };
        }
        // aggregate:  if_commit((aggregate_list(S, Ts, R), Target = R), rows_concat([Outs,[e(L)]], O), O = Outs)
        if (isC(C, ',', 2) && isC(D(C).a[0], 'aggregate_list', 3)) throw BackError('aggregate outside findall template');
        // det_prefix:  if_commit(B, Code(O), O = [])
        if (OF && OF.kind === 'none') {
          const inner = decompCode(T, OF.v, ctx);
          return { goal: conj([r(C), inner]), out: OF.v, next: i + 1 };
        }
        // ite_det:  if_commit(C, CodeT(O), CodeF(O))
        const Ot = findOut(T), Of = findOut(F);
        if (Ot && Of && Ot === Of) {
          const tg = decompCode(T, Ot, ctx), fg = decompCode(F, Of, ctx);
          // a scan with a deterministic prefix:  if_commit(Pre, q(Xs, e(L), O), CodeF(O))
          const tc = D(tg);
          const isScan = (T.length === 1 && scanOf(P.key(T[0]), ctx)) || (T.length === 2 && D(T[0]).t === 'c' && /__rows$/.test(D(T[0]).f) && scanOf(P.key(T[1]), ctx, D(T[0]).f.replace(/__rows$/, '')));
          if (isScan && tc.t === 'c' && tc.f === ';' && isC(tc.a[0], '->', 2) && show(tc.a[1]) === show(fg))
            return { goal: mkIte(conj([r(C), D(tc.a[0]).a[0]]), D(tc.a[0]).a[1], fg), out: Ot, next: i + 1 };
          return { goal: mkIte(r(C), tg, fg), out: Ot, next: i + 1 };
        }
        throw BackError('unrecognised if_commit/3');
      }
      if (k === 'effect_text/2') {
        const nx = gs[i + 1];
        if (isC(nx, '=', 2)) {
          const rhs = D(nx.a[1]); const l = listToArray(rhs);
          if (l && l.length === 2 && isC(l[0], 'out', 1)) return { goal: r(g.a[0]), out: D(nx.a[0]), next: i + 2 };
          // effect_prefix:  effect_text(B, T), Code(O1), O = [out(T)|O1]
        }
        // find O = [out(T)|O1]
        for (let j = i + 1; j < gs.length; j++) {
          const q = gs[j];
          if (isC(q, '=', 2) && isC(q.a[1], '.', 2) && isC(D(q.a[1]).a[0], 'out', 1) && D(D(D(q.a[1]).a[0]).a[0]) === D(g.a[1])) {
            const O1 = D(D(q.a[1]).a[1]);
            const rest = decompCode(gs.slice(i + 1, j), O1, ctx);
            return { goal: conj([r(g.a[0]), rest]), out: D(q.a[0]), next: j + 1 };
          }
        }
        throw BackError('effect_text without its out item');
      }
      if (k === 'builtin_rows/2') {
        const nx = gs[i + 1];
        if (!isC(nx, 'splice_extend', 4)) throw BackError('builtin_rows without splice_extend');
        return { goal: r(g.a[0]), out: D(nx.a[3]), next: i + 2 };
      }
      if (k === 'copy_term/2') {
        const a0 = D(g.a[0]);
        // findall / aggregate:  copy_term(f(e(L),T), f(EG,TG)), nm(EG,RG), packet_split, project_list, if_commit
        if (isC(a0, 'f', 2)) {
          const call = gs[i + 1], split = gs[i + 2], proj = gs[i + 3], fin = D(gs[i + 4]);
          if (!call || !isC(split, 'packet_split', 3) || !isC(proj, 'project_list', 4) || !isC(fin, 'if_commit', 3)) throw BackError('unrecognised findall pattern');
          const G = auxBody(P.key(call), null, ctx);
          const Tm = r(a0.a[1]);
          const out = findOut(flat(fin.a[1]));
          const cnd = D(fin.a[0]);
          if (isC(cnd, ',', 2) && isC(D(cnd.a[0]), 'aggregate_list', 3)) {
            const sp = D(D(cnd.a[0]).a[0]).n; const target = r(D(cnd.a[1]).a[0]);
            const spec = sp === 'count' ? Atom('count') : Cmp(sp, [Tm]);
            return { goal: Cmp('aggregate_all', [spec, G, target]), out, next: i + 5 };
          }
          return { goal: Cmp('findall', [Tm, G, r(D(cnd).a[0])]), out, next: i + 5 };
        }
        // disjunction:  copy_term(e(L),E1), d1(E1,R1), ..., rows_concat([R1..], O)
        // if-then-else: copy_term(e(L),EC), k(EC,RC), packet_first(RC,Pre,First), i(First,e(L),RB), rows_concat([Pre,RB],O)
        const call = gs[i + 1]; const nx2 = gs[i + 2];
        if (isC(nx2, 'packet_first', 3)) {
          const ic = gs[i + 3], rc = gs[i + 4];
          const Cg = auxBody(P.key(call), null, ctx);
          const ik = P.key(ic);
          const Fg = auxBody(ik, c => isA(D(c.head).a[0], '[]'), ctx);
          const Tg = auxBody(ik, c => isC(D(c.head).a[0], '.', 2), ctx);
          return { goal: mkIte(Cg, Tg, Fg), out: D(D(rc).a[1]), next: i + 5 };
        }
        // disjunction
        const alts = []; let j = i;
        while (j < gs.length && isC(gs[j], 'copy_term', 2) && isC(D(gs[j]).a[0], 'e', 1)) {
          alts.push(auxBody(P.key(gs[j + 1]), null, ctx)); j += 2;
        }
        const rc = gs[j];
        if (!isC(rc, 'rows_concat', 2) && !isC(rc, 'rows_concat_cut', 2)) throw BackError('unrecognised disjunction');
        let dg = alts[alts.length - 1]; for (let q = alts.length - 2; q >= 0; q--) dg = Cmp(';', [alts[q], dg]);
        return { goal: dg, out: D(D(rc).a[1]), next: j + 1 };
      }
      // facts scan:  p__rows(T), q(T, e(L), O)
      if (g.t === 'c' && g.a.length === 1 && /__rows$/.test(g.f) && gs[i + 1] && D(gs[i + 1]).t === 'c' && D(D(gs[i + 1]).a[0]) === D(g.a[0])) {
        const q = D(gs[i + 1]); const sc = scanOf(P.key(q), ctx, g.f.replace(/__rows$/, ''));
        if (sc) return { goal: mkIte(conj([sc.gen, sc.post]), sc.T, sc.F), out: D(q.a[2]), next: i + 2 };
      }
      // first-match scan:  q(Xs, e(L), O)
      if (g.t === 'c' && g.a.length === 3 && isC(g.a[1], 'e', 1)) {
        const sc = scanOf(P.key(g), ctx);
        if (sc) return { goal: mkIte(conj([Cmp('member', [sc.X, r(g.a[0])]), sc.post]), sc.T, sc.F), out: D(g.a[2]), next: i + 1 };
      }
      // user call:  q__cp(Args, P), splice_extend(P, Args, e(L), O)
      if (g.t === 'c' && /__cp$/.test(g.f)) {
        const nx = gs[i + 1];
        if (!isC(nx, 'splice_extend', 4)) throw BackError('call without splice_extend');
        const nm = g.f.replace(/__cp$/, '');
        return { goal: Cmp(nm, g.a.slice(0, -1).map(r)), out: D(nx.a[3]), next: i + 2 };
      }
      throw BackError('unrecognised goal ' + show(g, { varName: v => v.name || '_' }));
    }
    // nm(Xs, e(L), O) :- if_commit(Xs = [Y|Ys], if_commit((X = Y, Post), T, nm(Ys, e(L), O)), F)
    function scanOf(k, ctx, factsName) {
      const cls = prog.preds.get(k); if (!cls || cls.length !== 1) return null;
      const h = D(cls[0].head); const b = D(cls[0].body);
      if (!isC(b, 'if_commit', 3)) return null;
      const c1 = D(b.a[0]), inner = D(b.a[1]);
      if (!isC(c1, '=', 2) || D(c1.a[0]) !== D(h.a[0]) || !isC(c1.a[1], '.', 2) || !isC(inner, 'if_commit', 3)) return null;
      const Y = D(D(c1.a[1]).a[0]), Ys = D(D(c1.a[1]).a[1]);
      const cg = flat(inner.a[0]); const first = D(cg[0]);
      const rec = flat(inner.a[2]); if (rec.length !== 1 || P.key(rec[0]) !== k || D(D(rec[0]).a[0]) !== Ys) return null;
      const r = x => ren(x, ctx.names); const O = h.a[2];
      if (factsName) {
        if (!isC(first, 'copy_term', 2) || D(first.a[0]) !== Y) return null;
        return { gen: Cmp(factsName, listToArray(first.a[1]).map(r)), post: conj(cg.slice(1).map(r)), T: decompCode(flat(inner.a[1]), O, ctx), F: decompCode(flat(b.a[2]), O, ctx) };
      }
      if (!isC(first, '=', 2) || D(first.a[1]) !== Y) return null;
      return { X: r(first.a[0]), post: conj(cg.slice(1).map(r)), T: decompCode(flat(inner.a[1]), O, ctx), F: decompCode(flat(b.a[2]), O, ctx) };
    }
    function outOfSimple(gs) {
      if (gs.length !== 1) return null; const g = D(gs[0]);
      if (!isC(g, '=', 2)) return null; const rhs = D(g.a[1]);
      if (isA(rhs, '[]')) return { v: D(g.a[0]), kind: 'none' };
      const l = listToArray(rhs); if (l && l.length === 1 && isC(l[0], 'e', 1)) return { v: D(g.a[0]), kind: 'row' };
      return null;
    }
    // the variable a code sequence binds as its packet (its last output)
    function findOut(gs) {
      const g = D(gs[gs.length - 1]);
      if (isC(g, '=', 2)) return D(g.a[0]);
      if (isC(g, 'if_commit', 3)) { const t = flat(g.a[2]); return findOut(t); }
      if (isC(g, 'rows_concat', 2) || isC(g, 'rows_concat_cut', 2)) return D(g.a[1]);
      if (isC(g, 'splice_extend', 4)) return D(g.a[3]);
      if (g.t === 'c' && g.a.length >= 2) return D(g.a[g.a.length - 1]);
      return null;
    }
    function mkIte(C, T, F) {
      if (isA(T, 'fail') && isA(F, 'true')) return Cmp('\\+', [C]);
      if (isA(T, 'true') && isA(F, 'fail')) return Cmp('once', [C]);
      if (isA(T, 'true') && isA(F, 'true')) return Cmp('ignore', [C]);
      return Cmp(';', [Cmp('->', [C, T]), F]);
    }

    // rule CUT inverse: p(H..) :- ( [H..]=[h..], G -> B ; Rest )  ==>  p(h..) :- G, !, B.  + Rest
    function restoreCuts(clause, pname, pk) {
      const h = D(clause.head); const H = h.t === 'c' ? h.a.map(D) : [];
      const isMergedHead = H.length > 0 && H.every(v => v.t === 'v' && /^H__\d+$/.test(v.name || '')) || (H.length === 0 && /__c\d/.test(show(clause.body, { varName: v => v.name || '_' })));
      if (!isMergedHead) return [clause];
      const out = [];
      let b = D(clause.body);
      const headEq = g => { g = D(g); if (H.length === 0) return { ok: true, args: [], rest: g }; const gs = flat(g); const e0 = D(gs[0]); if (isC(e0, '=', 2) && listToArray(e0.a[0]) && listToArray(e0.a[0]).every((x, i) => D(x) === H[i])) return { ok: true, args: listToArray(e0.a[1]), rest: conj(gs.slice(1)) }; return { ok: false }; };
      for (;;) {
        if (isA(b, 'fail')) break;
        if (isC(b, ';', 2) && isC(D(b).a[0], '->', 2)) {
          const it = D(D(b).a[0]); const he = headEq(it.a[0]);
          if (!he.ok) return [clause];
          out.push({ head: Cmp(pname, he.args), body: conj([he.rest, Atom('!'), restoreLaterCuts(it.a[1])]) });
          b = D(D(b).a[1]); continue;
        }
        if (isC(b, 'once', 1)) { const he = headEq(D(b).a[0]); if (!he.ok) return [clause]; out.push({ head: Cmp(pname, he.args), body: conj([he.rest, Atom('!')]) }); break; }
        if (isC(b, ';', 2)) {
          const he = headEq(D(b).a[0]); if (!he.ok) return [clause];
          out.push({ head: Cmp(pname, he.args), body: he.rest }); b = D(D(b).a[1]); continue;
        }
        const he = headEq(b); if (!he.ok) return [clause];
        out.push({ head: Cmp(pname, he.args), body: he.rest }); break;
      }
      note(pk, 'cuts restored from the if_commit chain (rule CUT)');
      return out;
    }
    function restoreLaterCuts(g) {
      g = D(g);
      if (isC(g, ';', 2) && isC(D(g).a[0], '->', 2) && isA(D(g).a[1], 'fail')) { const it = D(D(g).a[0]); return conj([it.a[0], Atom('!'), restoreLaterCuts(it.a[1])]); }
      if (isC(g, 'once', 1)) return conj([g.a[0], Atom('!')]);
      return g;
    }
    // variable names: strip generated suffixes, anonymous singletons back to _
    function cleanup(c, pk) {
      const t = Cmp(':-', [c.head, c.body]);
      const counts = new Map();
      (function walk(x) { x = D(x); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') x.a.forEach(walk); })(t);
      const used = new Set();
      for (const v of counts.keys()) {
        let nm = v.name || '_';
        nm = nm.replace(/__c\d+$/, '');
        if (/^U__\d+$/.test(nm)) nm = counts.get(v) === 1 ? '_' : '_U' + nm.slice(3);
        else if (/^U__/.test(nm)) nm = '_' + nm.slice(3);
        else if (/^H__(\d+)$/.test(nm)) nm = 'H' + nm.slice(3);
        else if (/^L__[fb]$/.test(nm)) nm = 'L_';
        if (nm !== '_') { let base = nm, j = 2; while (used.has(nm)) nm = base + '_' + (j++); used.add(nm); }
        v.name = nm;
      }
      return { head: c.head, body: simplify(c.body) };
    }
    function simplify(g) {
      g = D(g);
      if (isC(g, ',', 2)) return conj(flat(g).map(simplify));
      if (isC(g, ';', 2)) { const a = simplify(g.a[0]), b = simplify(g.a[1]); if (isA(b, 'fail') && !isC(a, '->', 2)) return a; return Cmp(';', [a, b]); }
      if (isC(g, '->', 2)) return Cmp('->', [simplify(g.a[0]), simplify(g.a[1])]);
      if (isC(g, '\\+', 1)) {
        // \+ (C, \+ A)  ==>  forall(C, A)
        const inner = D(g.a[0]);
        if (isC(inner, ',', 2) && isC(D(inner.a[1]), '\\+', 1)) return Cmp('forall', [simplify(inner.a[0]), simplify(D(inner.a[1]).a[0])]);
        return Cmp('\\+', [simplify(g.a[0])]);
      }
      if (isC(g, 'findall', 3)) return Cmp('findall', [g.a[0], simplify(g.a[1]), g.a[2]]);
      return g;
    }

    // ---- fold specialised higher-order predicates back into maplist/foldl ----
    const specRe = /^(maplist|foldl|include|exclude|partition)_\w*__s\d+$/;
    const folded = new Map();
    for (const [pk, cls] of predClauses) {
      const nm = pk.slice(0, pk.lastIndexOf('/'));
      const m = specRe.exec(nm);
      if (!m || !cls || cls.length !== 2) continue;
      const kind = m[1];
      const c2 = cls[1]; const h2 = D(c2.head); const bg = flat(c2.body);
      const nL = h2.a.filter(x => isC(x, '.', 2)).length;
      let g0 = D(bg[0]); let extra, nListArgs, fvStart;
      if (kind === 'maplist') { extra = nL; nListArgs = nL; fvStart = nL; }
      else if (kind === 'foldl') { extra = nL + 2; nListArgs = nL + 2; fvStart = nL + 2; }
      else { // include/exclude/partition: ( G(X) -> ... ; ... )
        if (!(isC(g0, ';', 2) && isC(D(g0.a[0]), '->', 2))) continue;
        g0 = D(D(g0.a[0]).a[0]); extra = 1; nListArgs = kind === 'partition' ? 3 : 2; fvStart = nListArgs;
      }
      const fv = h2.a.slice(fvStart).map(D);
      let clo;
      if (/_lambda__s\d+$/.test(nm)) {
        // lambda: parameters are the list elements, body is every goal before the recursive call
        const elems = h2.a.slice(0, nL).map(x => D(x).a[0]);
        if (kind === 'foldl') elems.push(h2.a[nL], null);
        const bodyGoals = kind === 'maplist' || kind === 'foldl' ? bg.slice(0, -1) : [g0];
        let ps = elems.filter(Boolean);
        if (kind === 'foldl') { const nx = D(bg[bg.length - 1]).a[nL]; ps = h2.a.slice(0, nL).map(x => D(x).a[0]).concat([h2.a[nL], nx]); }
        clo = Cmp('>>', [list(ps), conj(bodyGoals)]);
      } else {
        if (g0.t !== 'c' && g0.t !== 'a') continue;
        const gargs = g0.t === 'c' ? g0.a : [];
        clo = gargs.length - extra === 0 ? Atom(P.name(g0)) : Cmp(P.name(g0), gargs.slice(0, gargs.length - extra));
      }
      folded.set(pk, { kind, arity: nListArgs + 1, clo, fv, nListArgs });
    }
    function foldCalls(g) {
      g = D(g);
      if (g.t === 'c' && [',', ';', '->', '\\+', 'findall', 'forall', 'once', 'ignore', 'aggregate_all'].includes(g.f)) return Cmp(g.f, g.a.map((x, i) => (g.f === 'findall' || g.f === 'aggregate_all') && i !== 1 ? x : foldCalls(x)));
      const k = P.key(g); const fi = folded.get(k);
      if (!fi) return g;
      const lists = g.a.slice(0, fi.nListArgs);
      const fvArgs = g.a.slice(lists.length);
      // substitute the spec's closure variables with the call's arguments
      const map = new Map(); fi.fv.forEach((v, i) => { if (v.t === 'v') map.set(v, fvArgs[i]); });
      const clo = subst(fi.clo, map);
      return Cmp(fi.kind, [clo].concat(lists));
    }
    function subst(t, map) { t = D(t); if (t.t === 'v') return map.has(t) ? map.get(t) : t; if (t.t === 'c') return Cmp(t.f, t.a.map(x => subst(x, map))); return t; }
    if (folded.size) {
      for (const [pk, cls] of predClauses) if (cls) for (const c of cls) c.body = foldCalls(c.body);
      for (const pk of folded.keys()) { res.notes.push('specialised ' + pk + ' folded back into ' + folded.get(pk).kind + '/' + folded.get(pk).arity); predClauses.delete(pk); }
    }

    // ---- assemble ----
    const lines = ['% Prolog back-converted from Detlog by pl2detlog.'];
    for (const [pk, cls] of predClauses) {
      if (/^\$query\d+\//.test(pk)) { if (cls && cls[0]) res.queries.push({ pred: pk, goal: P.show(cls[0].body, { varName: v => v.name }) }); continue; }
      res.preds.push({ key: pk, clauses: cls, notes: predNotes.get(pk) || [] });
      if (!cls) { lines.push('', '% ' + pk + ': not back-convertible'); continue; }
      lines.push('');
      for (const n of predNotes.get(pk) || []) lines.push('% ' + pk + ': ' + n);
      for (const c of cls) { const t = isA(c.body, 'true') ? c.head : Cmp(':-', [c.head, c.body]); lines.push(P.showClause(t, { varName: v => v.name && v.name !== '_' ? v.name : '_' })); res.clauses.push(t); }
    }
    res.text = lines.join('\n') + '\n';
    return res;
  }
  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }

  // ---- change warnings: compare back-converted Prolog with the original source, predicate by predicate ----
  function normText(src) {
    const prog = P.loadProgram(src); const m = new Map();
    for (const k of prog.order) {
      m.set(k, prog.preds.get(k).map(cl => {
        const mp = new Map(); const c = copy(Cmp(':-', [cl.head, cl.body]), mp);
        if (cl.vars) for (const [nm, v] of cl.vars) { const nv = mp.get(v); if (nv) nv.name = nm; }
        return canon(c);
      }));
    }
    return m;
  }
  // canonical text with variables numbered in order of appearance (names do not matter)
  function canon(t) { const nm = P.namer(); const b = D(t.a[1]); return isA(b, 'true') ? P.show(t.a[0], { varName: nm }) : P.show(t, { varName: nm }); }
  function changeWarnings(originalSrc, backText, backRes) {
    const o = normText(originalSrc), b = normText(backText);
    const warnings = [];
    for (const [k, ocls] of o) {
      const bcls = b.get(k);
      const notes = (backRes && (backRes.preds.find(p => p.key === k) || {}).notes) || [];
      if (!bcls) { const nb = backRes && backRes.preds.find(p => p.key === k); warnings.push({ pred: k, kind: nb && !nb.clauses ? 'error' : 'removed', msg: nb && !nb.clauses ? 'not back-convertible' : 'predicate is missing from the back-converted program', notes }); continue; }
      if (ocls.length === bcls.length && ocls.every((c, i) => c === bcls[i])) { warnings.push({ pred: k, kind: 'same', msg: 'unchanged', notes }); continue; }
      const diff = [];
      const n = Math.max(ocls.length, bcls.length);
      for (let i = 0; i < n; i++) if (ocls[i] !== bcls[i]) diff.push({ i: i + 1, was: ocls[i] || null, now: bcls[i] || null });
      warnings.push({ pred: k, kind: 'changed', msg: describeChange(ocls, bcls, notes), diff, notes });
    }
    for (const [k] of b) if (!o.has(k)) warnings.push({ pred: k, kind: 'added', msg: 'predicate added (not in the original source)', notes: [] });
    return warnings;
  }
  function describeChange(o, b, notes) {
    if (notes.some(n => /S2A/.test(n))) return 'rules replaced by their S2A answer table / formula (same answers for every call that raises no error)';
    const ot = o.join(' '), bt = b.join(' ');
    const reasons = [];
    if (/\bonce\(|\bignore\(|\bforall\(|\bcall\(/.test(ot) && !/\bonce\(|\bignore\(|\bforall\(|\bcall\(/.test(bt)) reasons.push('once/ignore/forall/call written as if-then-else');
    if (/\bnot\(/.test(ot)) reasons.push('not/1 written as \\+');
    if (/\bbagof\(|\bsetof\(/.test(ot)) reasons.push('bagof/setof written as findall');
    if (/\bphrase\(/.test(ot) && !/\bphrase\(/.test(bt)) reasons.push('phrase/2,3 written as a direct DCG call');
    if ((ot.match(/!/g) || []).length !== (bt.match(/!/g) || []).length) reasons.push('cut placement written as an if-then-else');
    if (/->/.test(bt) && !/->/.test(ot)) reasons.push('local cut written as an if-then-else');
    if (o.length !== b.length) reasons.push('number of clauses changed (' + o.length + ' -> ' + b.length + ')');
    return (reasons.length ? reasons.join('; ') : 'clause text changed') + ' — equivalence is checked by evaluation';
  }

  P.backConvert = backConvert; P.changeWarnings = changeWarnings; P.canonClauses = normText;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog algebra: rewrites that change the algorithm, each derived from first principles, with its
   proof obligation stated where it is used.  Shared by the source rewrites (rewrite.js), the JIT and the C
   export.

   pairwise(prog, key): is the test predicate key (one argument, a list) a conjunction over all pairs of
   positions?  That is, is it
       t([]).
       t([X|Xs]) :- r(X, Xs, C0), t(Xs).          (the two goals in either order)
       r(_, [], _).
       r(X, [Y|Ys], D) :- Tests(X, Y, D), D1 is D + 1, r(X, Ys, D1).
   with Tests a conjunction of integer comparisons over X, Y and D alone?  Then, unfolding both
   recursions on a proper list L = [L1, ..., Ln]:
       t(L)  <=>  for all i < j:  Tests(Li, Lj, C0 + (j - i - 1)).
   A conjunction over pairs is prefix-closed: if any pair inside a prefix fails, every completion of the
   prefix fails.  So a generator that builds L left to right may test each new element against those
   already placed, and drop the prefix at the first failure: the same lists pass, in the same order. */
(function (P) {
  'use strict';
  const D = P.deref;
  const CMP = { '=\\=': '!=', '=:=': '==', '<': '<', '>': '>', '=<': '<=', '>=': '>=' };
  const isV = t => D(t).t === 'v';
  const conjOf = b => P.flatConj ? P.flatConj(b).map(D) : (function f(g) { g = D(g); return g.t === 'c' && g.f === ',' && g.a.length === 2 ? f(g.a[0]).concat(f(g.a[1])) : [g]; })(b);
  const isNil = t => { t = D(t); return t.t === 'a' && t.n === '[]'; };
  const consOf = t => { t = D(t); return t.t === 'c' && t.f === '.' && t.a.length === 2 ? [D(t.a[0]), D(t.a[1])] : null; };
  const isTrue = b => { b = D(b); return b.t === 'a' && b.n === 'true'; };
  const keyOf = g => { g = D(g); return g.t === 'c' ? g.f + '/' + g.a.length : g.t === 'a' ? g.n + '/0' : null; };

  // an integer expression over the given variables, as a function from variable names to code
  function arithOK(t, vars) {
    t = D(t);
    if (t.t === 'n') return !t.f && Number.isSafeInteger(t.v);
    if (t.t === 'v') return vars.includes(t);
    return t.t === 'c' && ((t.a.length === 2 && ['+', '-', '*'].includes(t.f)) || (t.a.length === 1 && t.f === '-')) && t.a.every(a => arithOK(a, vars));
  }
  function arithCode(t, env) {
    t = D(t);
    if (t.t === 'n') return '(' + t.v + ')';
    if (t.t === 'v') return env.get(t);
    if (t.a.length === 1) return '(-' + arithCode(t.a[0], env) + ')';
    return '(' + arithCode(t.a[0], env) + ' ' + t.f + ' ' + arithCode(t.a[1], env) + ')';
  }

  function pairwise(prog, key) {
    const tc = prog.preds.get(key);
    if (!tc || tc.length !== 2 || +key.slice(key.lastIndexOf('/') + 1) !== 1) return null;
    const name = key.slice(0, key.lastIndexOf('/'));
    const base = tc.find(c => isNil(D(c.head).a[0]) && isTrue(c.body));
    const step = tc.find(c => c !== base);
    if (!base || !step) return null;
    const sc = consOf(D(step.head).a[0]); if (!sc || !isV(sc[0]) || !isV(sc[1]) || sc[0] === sc[1]) return null;
    const [X, Xs] = sc;
    const sb = conjOf(step.body); if (sb.length !== 2) return null;
    const self = sb.find(g => keyOf(g) === key), rel = sb.find(g => g !== self);
    if (!self || !rel || D(self.a[0]) !== Xs) return null;
    const rk = keyOf(rel); if (!rk || !rk.endsWith('/3') || rk === key) return null;
    if (D(rel.a[0]) !== X || D(rel.a[1]) !== Xs) return null;
    const c0 = D(rel.a[2]); if (c0.t !== 'n' || c0.f || !Number.isSafeInteger(c0.v)) return null;
    const rc = prog.preds.get(rk);
    if (!rc || rc.length !== 2) return null;
    const rbase = rc.find(c => isNil(D(c.head).a[1]) && isTrue(c.body) && isV(D(c.head).a[0]) && isV(D(c.head).a[2]));
    const rstep = rc.find(c => c !== rbase);
    if (!rbase || !rstep) return null;
    const h = D(rstep.head); const Q = D(h.a[0]), Dv = D(h.a[2]); const yc = consOf(h.a[1]);
    if (!isV(Q) || !isV(Dv) || !yc || !isV(yc[0]) || !isV(yc[1])) return null;
    const [Y, Ys] = yc;
    if (new Set([Q, Dv, Y, Ys]).size !== 4) return null;
    const rb = conjOf(rstep.body);
    const rec = rb[rb.length - 1];
    if (keyOf(rec) !== rk || D(rec.a[0]) !== Q || D(rec.a[1]) !== Ys) return null;
    const D1 = D(rec.a[2]); if (!isV(D1)) return null;
    const inc = rb[rb.length - 2];
    if (!inc || keyOf(inc) !== 'is/2' || D(inc.a[0]) !== D1) return null;
    const ie = D(inc.a[1]);
    const plus1 = ie.t === 'c' && ie.f === '+' && ie.a.length === 2 && ((D(ie.a[0]) === Dv && D(ie.a[1]).t === 'n' && D(ie.a[1]).v === 1) || (D(ie.a[1]) === Dv && D(ie.a[0]).t === 'n' && D(ie.a[0]).v === 1));
    if (!plus1) return null;
    const tests = rb.slice(0, -2);
    for (const g of tests) {
      if (g.t !== 'c' || g.a.length !== 2 || !CMP[g.f]) return null;
      if (!g.a.every(a => arithOK(a, [Q, Y, Dv]))) return null;
    }
    return {
      name, key, rel: rk, c0: c0.v, tests,
      // C (or JavaScript) for Tests(prev, next, dist): integer expressions in, a condition out
      code: (prev, next, dist, js) => tests.length ? tests.map(g => '(' + arithCode(g.a[0], new Map([[Q, prev], [Y, next], [Dv, dist]])) + ' ' + (js ? ({ '!=': '!==', '==': '===' })[CMP[g.f]] || CMP[g.f] : CMP[g.f]) + ' ' + arithCode(g.a[1], new Map([[Q, prev], [Y, next], [Dv, dist]])) + ')').join(' && ') : '1',
      proof: 'pairwise test: ' + name + '(L) holds iff for all i < j, ' + tests.map(g => P.show(g)).join(', ') + ' with ' + P.show(Q) + ' = L_i, ' + P.show(Y) + ' = L_j, ' + P.show(Dv) + ' = ' + c0.v + ' + (j - i - 1) (unfolding ' + key + ' and ' + rk + '); a conjunction over pairs is prefix-closed, so each new element is tested against those placed and a failing prefix is dropped'
    };
  }

  P.pairwise = pairwise;
  P.algebra = { arithOK, arithCode, conjOf, keyOf, consOf, isNil };
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog source rewrites (MNN): Prolog to Prolog, before conversion, each derived from first principles.
   rewrite(src) -> { text, steps: [{ pred, rule, proof }] }; text is src itself when nothing applies.

   1. Solve for the last generator.  In a body  ..., between(Lo, Hi, X), E1 =:= E2, ...  (or a one-clause
      predicate that is such a between/3, unfolded) where X is a variable that appears once in E1 =:= E2, as
      +X or -X in a sum, and every other variable of the test is an integer bound by an earlier goal:
        E1 =:= E2  <=>  X = S  for the one integer S that isolates X (E1 - E2 is linear in X with
        coefficient +1 or -1), and between/3 enumerates each integer of [Lo, Hi] once, in order.
      So  between(Lo, Hi, X), E1 =:= E2  has the same answers, in the same order, as
          X is S, Lo =< X, X =< Hi
      (at most one answer instead of a search over Hi - Lo + 1 values).

   2. Accumulate an appended result.  A predicate
        p([], []).
        p([H|T], R) :- p(T, RT), append(RT, E, R).     (append/3, or a predicate that is append: see below)
      with E a closed list whose variables are H's, computes p(L) = p(T) ++ E.  Let acc(L, A) = p(L) ++ A.
      Then  acc([], A) = A  and  acc([H|T], A) = (p(T) ++ E) ++ A = p(T) ++ (E ++ A) = acc(T, E ++ A),
      by the associativity of ++ on proper lists, and p(L) = acc(L, []).  For a proper list L that is
        p__acc([], A, A).
        p__acc([H|T], A, R) :- p__acc(T, [e1, ..., ek|A], R).
      which is linear where p is quadratic.  Both are deterministic on a proper list, and the result is
      unified with R once it is complete in both, so a bound R gives the same answer.  For any other L
      (a partial list, a variable) p keeps its own clauses:  p(L, R) :- ( is_list(L) -> p__acc(L, [], R)
      ; p__orig(L, R) ).
      A predicate is append when its clauses are, up to renaming,
        a([], L, L).   a([H|T], L, [H|R]) :- a(T, L, R).

   3. Fuse a map into the fold that reads it.  In a body  ..., maplist(F, L, D), foldl(G, D, A0, S), ...
      (either goal may be a one-clause predicate that is just that call, unfolded) where
        F(X, Y) :- Y is E1.     (E1's only variable is X)
        G(Y, B0, B) :- B is E2.  (E2's variables are among Y, B0)   and A0 is a number,
      both goals walk the same list D element by element, so by induction on the length of L
        maplist(F, L, D), foldl(G, D, A0, S)  <=>  mf(L, D, A0, S)  where
        mf([], [], A, A).
        mf([X|Xs], [Y|Ys], B0, B) :- Y is E1, B1 is E2, mf(Xs, Ys, B1, B).
      Same answers in the same order (for an unbound L both enumerate lists by length), and the same
      errors: an error can only come from Y is E1 (X not a number), since Y and B0 are then numbers and
      B is E2 cannot fail or raise; that error is met on the same element in both. D is still built. */
(function (P) {
  'use strict';
  const D = P.deref;
  const { Cmp, Int, Atom, Var, show } = P;
  const isV = t => D(t).t === 'v';
  const keyOf = g => { g = D(g); return g.t === 'c' ? g.f + '/' + g.a.length : g.t === 'a' ? g.n + '/0' : null; };
  const conj = gs => gs.reduce((a, g) => (a ? Cmp(',', [a, g]) : g), null) || Atom('true');
  const flat = b => { b = D(b); return b.t === 'c' && b.f === ',' && b.a.length === 2 ? flat(b.a[0]).concat(flat(b.a[1])) : [b]; };
  const isNil = t => { t = D(t); return t.t === 'a' && t.n === '[]'; };
  const consOf = t => { t = D(t); return t.t === 'c' && t.f === '.' && t.a.length === 2 ? [D(t.a[0]), D(t.a[1])] : null; };
  const isTrue = b => { b = D(b); return b.t === 'a' && b.n === 'true'; };
  const intC = t => { t = D(t); return t.t === 'n' && !t.f && Number.isSafeInteger(t.v); };
  const occurs = (v, t) => { t = D(t); return t === v || (t.t === 'c' && t.a.some(a => occurs(v, a))); };
  const vars = t => P.termVars(t).map(D);

  // ---- 1. solve for the last generator ----
  // between(Lo, Hi, X) itself, or a call of a one-clause predicate g(V) :- between(Lo, Hi, V)
  function generator(prog, g) {
    g = D(g);
    if (keyOf(g) === 'between/3' && intC(g.a[0]) && intC(g.a[1]) && isV(g.a[2])) return { lo: D(g.a[0]).v, hi: D(g.a[1]).v, x: D(g.a[2]) };
    const k = keyOf(g); const cls = k && prog.preds.get(k);
    if (!cls || cls.length !== 1 || g.a.length !== 1 || !isV(g.a[0])) return null;
    const h = D(cls[0].head), b = D(cls[0].body);
    if (!isV(h.a[0]) || keyOf(b) !== 'between/3' || !intC(b.a[0]) || !intC(b.a[1]) || D(b.a[2]) !== D(h.a[0])) return null;
    return { lo: D(b.a[0]).v, hi: D(b.a[1]).v, x: D(g.a[0]), unfolded: k };
  }
  // the coefficient (+1 or -1) of X in an additive expression where X appears once, or 0 if not of that form
  function coef(t, x) {
    t = D(t);
    if (t === x) return 1;
    if (!occurs(x, t)) return 0;
    if (t.t === 'c' && t.a.length === 2 && t.f === '+') return coef(t.a[0], x) || coef(t.a[1], x);
    if (t.t === 'c' && t.a.length === 2 && t.f === '-') return coef(t.a[0], x) || -coef(t.a[1], x);
    if (t.t === 'c' && t.a.length === 1 && t.f === '-') return -coef(t.a[0], x);
    return NaN; // X under * or a function: not linear with a unit coefficient
  }
  const arith = t => { t = D(t); return t.t === 'v' || intC(t) || (t.t === 'c' && ((t.a.length === 2 && ['+', '-', '*'].includes(t.f)) || (t.a.length === 1 && t.f === '-')) && t.a.every(arith)); };
  // t with X replaced by 0, simplified where 0 was added or subtracted
  function zero(t, x) {
    t = D(t);
    if (t === x) return Int(0);
    if (t.t !== 'c') return t;
    const a = t.a.map(u => zero(u, x));
    const z = u => intC(u) && D(u).v === 0;
    if (t.f === '+' && a.length === 2) { if (z(a[0])) return a[1]; if (z(a[1])) return a[0]; }
    if (t.f === '-' && a.length === 2 && z(a[1])) return a[0];
    if (t.f === '-' && a.length === 1 && z(a[0])) return Int(0);
    return Cmp(t.f, a);
  }
  function solveBody(prog, gs, steps, k) {
    let changed = false;
    for (let i = 0; i + 1 < gs.length; i++) {
      const gen = generator(prog, gs[i]); if (!gen) continue;
      const t = D(gs[i + 1]); if (keyOf(t) !== '=:=/2') continue;
      const x = gen.x;
      if (gs.slice(0, i).some(g => occurs(x, g))) continue;
      const [e1, e2] = t.a.map(D);
      if (!arith(e1) || !arith(e2)) continue;
      const c1 = coef(e1, x), c2 = coef(e2, x);
      if (Number.isNaN(c1) || Number.isNaN(c2) || Math.abs(c1) + Math.abs(c2) !== 1) continue;
      // every other variable of the test: an integer from an earlier generator or is/2
      const before = gs.slice(0, i);
      const ints = new Set(before.flatMap(g => { const gg = generator(prog, g); if (gg) return [gg.x]; g = D(g); return keyOf(g) === 'is/2' && isV(g.a[0]) ? [D(g.a[0])] : []; }));
      if (!vars(t).filter(v => v !== x).every(v => ints.has(v))) continue;
      // E1 - E2 = s*X + R  =>  X = -s*R;  R = zero(E1) - zero(E2)
      const s = c1 || -c2;
      const R1 = zero(e1, x), R2 = zero(e2, x);
      const S = s === 1 ? Cmp('-', [R2, R1]) : Cmp('-', [R1, R2]);
      const solved = (intC(R1) && D(R1).v === 0) ? (s === 1 ? R2 : Cmp('-', [Int(0), R2])) : (intC(R2) && D(R2).v === 0 && s === -1) ? R1 : S;
      const repl = [Cmp('is', [x, solved]), Cmp('=<', [Int(gen.lo), x]), Cmp('=<', [x, Int(gen.hi)])];
      steps.push({ pred: k, rule: 'solve', proof: 'solve for the last generator: ' + show(gs[i]) + ', ' + show(t) + '  =>  ' + repl.map(g => show(g)).join(', ') + '  (' + show(t) + ' is linear in ' + show(x) + ' with coefficient ' + (s > 0 ? '+1' : '-1') + ' and its other variables are integers bound before; between(' + gen.lo + ', ' + gen.hi + ', ' + show(x) + ') enumerates each integer once, in order, so the one value that satisfies the test is kept if it is in range)' });
      gs.splice(i, 2, ...repl);
      changed = true;
    }
    return changed;
  }

  // ---- 2. accumulate an appended result ----
  function isAppend(prog, k) {
    if (k === 'append/3') return true;
    const cls = prog.preds.get(k); if (!cls || cls.length !== 2 || !k.endsWith('/3')) return false;
    const [b, r] = cls;
    const hb = D(b.head); if (!isTrue(b.body) || !isNil(hb.a[0]) || !isV(hb.a[1]) || D(hb.a[1]) !== D(hb.a[2])) return false;
    const hr = D(r.head); const x = consOf(hr.a[0]), z = consOf(hr.a[2]); const L = D(hr.a[1]);
    if (!x || !z || !isV(x[0]) || !isV(x[1]) || !isV(L) || z[0] !== x[0] || !isV(z[1])) return false;
    const body = flat(r.body); if (body.length !== 1 || keyOf(body[0]) !== k) return false;
    const c = D(body[0]); return D(c.a[0]) === x[1] && D(c.a[1]) === L && D(c.a[2]) === z[1] && new Set([x[0], x[1], L, z[1]]).size === 4;
  }
  function closedList(t) { const out = []; t = D(t); while (t.t === 'c' && t.f === '.' && t.a.length === 2) { out.push(D(t.a[0])); t = D(t.a[1]); } return isNil(t) ? out : null; }
  function accumulate(prog, k, steps) {
    if (!k.endsWith('/2') || prog.dynamic.has(k)) return null;
    const cls = prog.preds.get(k); if (!cls || cls.length !== 2) return null;
    const name = k.slice(0, -2);
    const base = cls.find(c => isTrue(c.body) && isNil(D(c.head).a[0]) && isNil(D(c.head).a[1]));
    const rec = cls.find(c => c !== base); if (!base || !rec || cls.indexOf(base) !== 0) return null;
    const h = D(rec.head); const ht = consOf(h.a[0]); const R = D(h.a[1]);
    if (!ht || !isV(ht[0]) || !isV(ht[1]) || !isV(R) || ht[0] === ht[1] || R === ht[0] || R === ht[1]) return null;
    const [H, T] = ht;
    const body = flat(rec.body); if (body.length !== 2) return null;
    const [call, app] = body.map(D);
    if (keyOf(call) !== k || D(call.a[0]) !== T || !isV(call.a[1])) return null;
    const RT = D(call.a[1]);
    if (!isAppend(prog, keyOf(app)) || D(app.a[0]) !== RT || D(app.a[2]) !== R) return null;
    const E = closedList(app.a[1]);
    if (!E || E.some(e => vars(e).some(v => v !== H)) || [RT, R, T].some(v => occurs(v, app.a[1]))) return null;
    // the clauses
    const acc = name + '__acc', orig = name + '__orig';
    const L = Var('L'), Rr = Var('R'), A = Var('A'), H2 = Var('H'), T2 = Var('T'), R2 = Var('R');
    const sub = new Map([[H, H2]]);
    const copyE = t => { t = D(t); if (t.t === 'v') return sub.get(t) || t; if (t.t === 'c') return Cmp(t.f, t.a.map(copyE)); return t; };
    let accA = A; for (let i = E.length - 1; i >= 0; i--) accA = Cmp('.', [copyE(E[i]), accA]);
    const A2 = Var('A');
    const clauses = [
      Cmp(':-', [Cmp(name, [L, Rr]), Cmp(';', [Cmp('->', [Cmp('is_list', [L]), Cmp(acc, [L, Atom('[]'), Rr])]), Cmp(orig, [L, Rr])])]),
      Cmp(acc, [Atom('[]'), A2, A2]),
      Cmp(':-', [Cmp(acc, [Cmp('.', [H2, T2]), A, R2]), Cmp(acc, [T2, accA, R2])])
    ];
    // the original clauses, renamed (their recursive call too)
    const ren = t => { t = D(t); if (t.t === 'c') { const a = t.a.map(ren); return Cmp(t.f === name && t.a.length === 2 ? orig : t.f, a); } if (t.t === 'a' && t.n === name) return t; return t; };
    for (const c of cls) clauses.push(isTrue(c.body) ? ren(c.head) : Cmp(':-', [ren(c.head), ren(c.body)]));
    steps.push({ pred: k, rule: 'accumulate', proof: 'accumulate the appended result of ' + k + ': p([H|T]) = p(T) ++ ' + show(app.a[1]) + '; with acc(L, A) = p(L) ++ A, acc([], A) = A and acc([H|T], A) = acc(T, ' + show(accA) + ') by the associativity of ++, and p(L) = acc(L, []) for a proper list L; any other L runs ' + k + "'s own clauses (" + orig + ')' });
    return clauses;
  }

  // ---- 3. fuse a map into the fold that reads it ----
  // a goal that is Call itself or a one-clause predicate whose body is just Call (args renamed)
  function unfoldTo(prog, g, want, n) {
    g = D(g);
    if (keyOf(g) === want) return g.a;
    const k = keyOf(g); const cls = k && prog.preds.get(k); if (!cls || cls.length !== 1 || prog.dynamic.has(k)) return null;
    const h = D(cls[0].head), b = D(cls[0].body);
    if (keyOf(b) !== want || !h.a.every(isV) || new Set(h.a.map(D)).size !== h.a.length) return null;
    const m = new Map(h.a.map((v, i) => [D(v), D(g.a[i])]));
    const out = b.a.map(x => { x = D(x); if (x.t === 'v') return m.has(x) ? m.get(x) : null; return vars(x).length ? null : x; });
    return out.every(x => x) ? out : null;
  }
  // F(X, Y) :- Y is E (E's variables among ins)  ->  { params, e }
  function isFn(prog, f, n) {
    f = D(f); if (f.t !== 'a') return null;
    const cls = prog.preds.get(f.n + '/' + n); if (!cls || cls.length !== 1 || prog.dynamic.has(f.n + '/' + n)) return null;
    const h = D(cls[0].head), b = D(cls[0].body);
    if (!h.a.every(isV) || new Set(h.a.map(D)).size !== n || keyOf(b) !== 'is/2' || D(b.a[0]) !== D(h.a[n - 1])) return null;
    const e = D(b.a[1]); const ins = h.a.slice(0, n - 1).map(D);
    if (!vars(e).every(v => ins.includes(v))) return null;
    return { params: h.a.map(D), e };
  }
  function fuseBody(prog, gs, steps, k, extra) {
    let changed = false;
    for (let i = 0; i + 1 < gs.length; i++) {
      const m = unfoldTo(prog, gs[i], 'maplist/3'), f = m && unfoldTo(prog, gs[i + 1], 'foldl/4'); if (!m || !f) continue;
      const [F, L, Dl] = m, [G, D2, A0, S] = f;
      if (!isV(Dl) || D(D2) !== D(Dl) || !isV(S) || D(A0).t !== 'n' || D(L) === D(Dl) || D(S) === D(Dl) || D(S) === D(L)) continue;
      const fF = isFn(prog, F, 2), fG = isFn(prog, G, 3); if (!fF || !fG) continue;
      const name = D(F).n + '__' + D(G).n + '__mapfold';
      if (!extra.has(name)) {
        const X = Var('X'), Xs = Var('Xs'), Y = Var('Y'), Ys = Var('Ys'), B0 = Var('B0'), B1 = Var('B1'), B = Var('B'), A = Var('A');
        const sub = (t, m) => { t = D(t); if (t.t === 'v') return m.get(t) || t; if (t.t === 'c') return Cmp(t.f, t.a.map(u => sub(u, m))); return t; };
        const e1 = sub(fF.e, new Map([[fF.params[0], X]])), e2 = sub(fG.e, new Map([[fG.params[0], Y], [fG.params[1], B0]]));
        extra.set(name, [Cmp(name, [Atom('[]'), Atom('[]'), A, A]),
          Cmp(':-', [Cmp(name, [Cmp('.', [X, Xs]), Cmp('.', [Y, Ys]), B0, B]), conj([Cmp('is', [Y, e1]), Cmp('is', [B1, e2]), Cmp(name, [Xs, Ys, B1, B])])])]);
      }
      const g = Cmp(name, [D(L), D(Dl), D(A0), D(S)]);
      steps.push({ pred: k, rule: 'mapfold', proof: 'fuse the map into the fold: ' + show(gs[i]) + ', ' + show(gs[i + 1]) + '  =>  ' + show(g) + '  (maplist(' + show(F) + ') and foldl(' + show(G) + ') walk the same list; by induction on its length one walk computes both, with the same answers, order and errors, since ' + show(G) + ' is an is/2 on numbers that cannot fail or raise)' });
      gs.splice(i, 2, g); changed = true;
    }
    return changed;
  }
  // a query's goal, fused where rule 3 applies; the new predicates are added to prog
  function fuseQuery(prog, term, steps) {
    const gs = flat(term), extra = new Map();
    if (!fuseBody(prog, gs, steps, 'query', extra)) return term;
    for (const cls of extra.values()) if (!prog.preds.has(keyOf(cls[0]))) for (const c of cls) prog.add(c, null);
    return conj(gs);
  }
  P.fuseQuery = fuseQuery;

  function rewrite(src) {
    let prog;
    try { prog = P.loadProgram(src); } catch (e) { return { text: src, steps: [] }; }
    const steps = [];
    const replaced = new Map(); // key -> clause terms
    const extra = new Map(); // fused predicates (rule 3)
    for (const k of prog.order) {
      const cls = prog.preds.get(k);
      const acc = accumulate(prog, k, steps);
      if (acc) { replaced.set(k, acc); continue; }
      let changed = false;
      const out = cls.map(c => {
        if (isTrue(c.body)) return c.head;
        const gs = flat(c.body);
        const a = solveBody(prog, gs, steps, k), b = fuseBody(prog, gs, steps, k, extra);
        if (a || b) { changed = true; return Cmp(':-', [c.head, conj(gs)]); }
        return Cmp(':-', [c.head, c.body]);
      });
      if (changed) replaced.set(k, out);
    }
    if (!steps.length) return { text: src, steps };
    // the program again: directives, then each predicate's clauses (rewritten ones as terms)
    const nm = () => { const names = new Map(); return v => { if (v.name && v.name !== '_' && !names.has(v)) { let n = v.name.replace(/^_+/, '') || 'V'; if (!/^[A-Z]/.test(n)) n = 'V' + n; const used = new Set(names.values()); let m = n, i = 1; while (used.has(m)) m = n + (i++); names.set(v, m); } if (!names.has(v)) names.set(v, '_G' + names.size); return names.get(v); }; };
    const lines = prog.directives.map(d => ':- ' + show(d, { quoted: true }) + '.');
    for (const k of prog.order) {
      const cls = replaced.get(k) || prog.preds.get(k).map(c => (isTrue(c.body) ? c.head : Cmp(':-', [c.head, c.body])));
      for (const c of cls) lines.push(show(c, { quoted: true, varName: nm() }) + '.');
    }
    for (const [name, cls] of extra) if (!prog.preds.has(name + '/4')) for (const c of cls) lines.push(show(c, { quoted: true, varName: nm() }) + '.');
    return { text: lines.join('\n') + '\n', steps };
  }

  P.rewrite = rewrite;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog C generator: Detlog -> C.  One C function per Detlog predicate selects the clause
   by its first argument and commits to it (no choicepoint); if_commit/3 becomes a trail mark,
   the condition, and an undo before the else branch. */
(function (P) {
  'use strict';
  const { deref, listToArray, show } = P;
  const D = deref;
  const RT = { // Detlog runtime predicate -> C function
    'rows_concat/2': 'rt_rows_concat', 'splice_extend/4': 'rt_splice_extend', 'project_rows/4': 'rt_project_rows', 'project_list/4': 'rt_project_list',
    'packet_first/3': 'rt_packet_first', 'packet_split/3': 'rt_packet_split', 'effect_text/2': 'rt_effect_text', 'builtin_rows/2': 'rt_builtin_rows',
    'cp_filter/3': 'rt_cp_filter', 'aggregate_list/3': 'rt_aggregate_list', 'splice_safe/2': 'rt_splice_safe', 'splice2/6': 'rt_splice2',
    'memo_lookup/3': 'rt_memo_lookup', 'rows_concat_cut/2': 'rt_rows_concat_cut', 'rows_cut_concat/2': 'rt_rows_cut_concat', 'strip_cut/2': 'rt_strip_cut', 'cut_in/2': 'rt_cut_in', 'memo_store/3': 'rt_memo_store', 's2a_rows/3': 'rt_s2a_rows'
  };
  const C_BUILTINS = new Set(['=/2', '\\=/2', '==/2', '\\==/2', '@</2', '@>/2', '@=</2', '@>=/2', 'compare/3', 'is/2', '=:=/2', '=\\=/2', '</2', '>/2', '=</2', '>=/2',
    'true/0', 'fail/0', 'false/0', 'var/1', 'nonvar/1', 'atom/1', 'number/1', 'integer/1', 'float/1', 'atomic/1', 'compound/1', 'callable/1', 'string/1', 'is_list/1', 'ground/1',
    'copy_term/2', 'functor/3', 'arg/3', '=../2', 'succ/2', 'plus/3', 'length/2', 'reverse/2', 'msort/2', 'sort/2', 'sum_list/2', 'sumlist/2', 'max_list/2', 'min_list/2',
    'nth0/3', 'nth1/3', 'last/2', 'memberchk/2', 'numlist/3', 'atom_length/2', 'string_length/2', 'atom_codes/2', 'atom_chars/2', 'string_codes/2', 'string_chars/2',
    'char_code/2', 'atom_number/2', 'number_codes/2', 'atom_string/2', 'string_concat/3', 'atomic_list_concat/2', 'atomic_list_concat/3', 'upcase_atom/2', 'downcase_atom/2',
    'term_to_atom/2', 'throw/1', 'code_type/2', 'split_string/4']);
  const C_ROWS = new Set(['permutation/2', 'atom_concat/3', 'char_type/2', 'member/2', 'between/3', 'append/3', 'select/3', 'nth0/3', 'nth1/3', 'length/2', 'last/2', 'arg/3']);
  const C_EFFECTS = new Set(['write/1', 'print/1', 'writeq/1', 'write_canonical/1', 'write_term/2', 'writeln/1', 'nl/0', 'tab/1', 'put_char/1', 'format/1', 'format/2', 'format/3', 'flush_output/0']);

  function mangle(s) { return s.replace(/[^A-Za-z0-9_]/g, c => '_' + c.charCodeAt(0).toString(16).toUpperCase().padStart(2, '0')); }
  function cstr(s) {
    let o = '"';
    for (const ch of Buffer_from(s)) {
      if (ch === 34) o += '\\"'; else if (ch === 92) o += '\\\\'; else if (ch === 10) o += '\\n'; else if (ch === 9) o += '\\t'; else if (ch === 13) o += '\\r';
      else if (ch < 32 || ch === 127) o += '\\' + ch.toString(8).padStart(3, '0');
      else if (ch === 63) o += '\\?';
      else o += String.fromCharCode(ch);
    }
    return o + '"';
  }
  // UTF-8 bytes (works in browsers and node)
  function Buffer_from(s) { const bytes = []; const enc = typeof TextEncoder !== 'undefined' ? new TextEncoder().encode(s) : null; if (enc) { for (const b of enc) bytes.push(b); return bytes; } for (const c of unescape(encodeURIComponent(s))) bytes.push(c.charCodeAt(0)); return bytes; }
  // strings in C source must stay byte strings: emit non-ASCII bytes as octal escapes
  function cstrBytes(s) { let o = '"'; for (const b of Buffer_from(s)) { if (b === 34) o += '\\"'; else if (b === 92) o += '\\\\'; else if (b === 10) o += '\\n'; else if (b === 9) o += '\\t'; else if (b < 32 || b >= 127 || b === 63) o += '\\' + b.toString(8).padStart(3, '0'); else o += String.fromCharCode(b); } return o + '"'; }

  // run-time support for native functions: bail-out by longjmp to the entry, integer helpers that bail where
  // the generic code would raise an error, ground equality, and tables for memoised calls on an integer
  const NATIVE_C = `
/* ---------- native tier ---------- */
#include <setjmp.h>
/* an input the native function may take: any bound term when unchecked (the contract says it is ground) */
#ifdef DL_CHECKED
#define DL_GROUND(t) is_ground(t)
#else
#define DL_GROUND(t) 1
#endif
/* GCC and Clang have a light setjmp (frame, stack and resume address only); otherwise the standard one */
#if defined(__GNUC__)
typedef void *nat_jmp[5];
#define NAT_SETJMP(b) __builtin_setjmp(b)
#define NAT_LONGJMP(b) __builtin_longjmp(b, 1)
#else
typedef jmp_buf nat_jmp;
#define NAT_SETJMP(b) setjmp(b)
#define NAT_LONGJMP(b) longjmp(b, 1)
#endif
static nat_jmp *nat_jb; static long nat_epoch = 0;
static void nat_bail(void) __attribute__((noinline));
static void nat_bail(void) { NAT_LONGJMP(*nat_jb); }
#ifdef DL_CHECKED
static long long n_iv(Term *x) { x = deref(x); if (x->tag != T_INT) nat_bail(); return x->iv; }
#else
/* unchecked (the default): the type contract is assumed, so no tag test */
static inline long long n_iv(Term *x) { return deref(x)->iv; }
#endif
static int n_isv(Term *x, long long v) { x = deref(x); return x->tag == T_INT && x->iv == v; }
static int n_eq(Term *a, Term *b) {
  a = deref(a); b = deref(b); if (a == b) return 1; if (a->tag != b->tag) return 0;
  switch (a->tag) {
    case T_INT: return a->iv == b->iv; case T_FLT: return a->fv == b->fv; case T_STR: return !strcmp(a->name, b->name);
    case T_ATOM: return a->name == b->name;
    case T_CMP: if (a->name != b->name || a->arity != b->arity) return 0; for (int i = 0; i < a->arity; i++) if (!n_eq(a->args[i], b->args[i])) return 0; return 1;
  }
  return 0;
}
#ifdef DL_CHECKED
static long long n_idiv(long long a, long long b) { if (b == 0) nat_bail(); return a / b; }
#else
static inline long long n_idiv(long long a, long long b) { return a / b; } /* unchecked: no zero test */
#endif
#ifdef DL_CHECKED
static long long n_iadd(long long a, long long b) { long long r; if (__builtin_add_overflow(a, b, &r)) nat_bail(); return r; }
#else
#define n_iadd(a, b) ((a) + (b)) /* unchecked: no overflow test */
#endif
#ifdef DL_CHECKED
static long long n_isub(long long a, long long b) { long long r; if (__builtin_sub_overflow(a, b, &r)) nat_bail(); return r; }
#else
#define n_isub(a, b) ((a) - (b)) /* unchecked: no overflow test */
#endif
#ifdef DL_CHECKED
static long long n_imul(long long a, long long b) { long long r; if (__builtin_mul_overflow(a, b, &r)) nat_bail(); return r; }
#else
#define n_imul(a, b) ((a) * (b)) /* unchecked: no overflow test */
#endif
#ifdef DL_CHECKED
static long long n_imod(long long a, long long b) { if (b == 0) nat_bail(); long long m = a % b; if (m != 0 && ((m < 0) != (b < 0))) m += b; return m; }
#else
static inline long long n_imod(long long a, long long b) { long long m = a % b; if (m != 0 && ((m < 0) != (b < 0))) m += b; return m; }
#endif
#ifdef DL_CHECKED
static long long n_irem(long long a, long long b) { if (b == 0) nat_bail(); return a % b; }
#else
static inline long long n_irem(long long a, long long b) { return a % b; } /* unchecked: no zero test */
#endif
static long long n_min(long long a, long long b) { return a <= b ? a : b; }
static long long n_max(long long a, long long b) { return a >= b ? a : b; }
typedef struct { long long key; long ep; int st; long long iv; Term *tv; } NMS;
typedef struct { NMS *s; size_t cap, n; long ep; } NMT;
static size_t nmt_h(long long k, size_t cap) { return (size_t)(((unsigned long long)k * 0x9E3779B97F4A7C15ULL) >> 17) & (cap - 1); }
static NMS *nmt_get(NMT *t, long long k) {
  if (!t->s || t->ep != nat_epoch) return NULL;
  for (size_t i = nmt_h(k, t->cap);; i = (i + 1) & (t->cap - 1)) { NMS *s = &t->s[i]; if (s->ep != nat_epoch) return NULL; if (s->key == k) return s; }
}
static void nmt_put(NMT *t, long long k, int st, long long iv, Term *tv) {
  if (t->ep != nat_epoch) { t->ep = nat_epoch; t->n = 0; if (t->s) memset(t->s, 0, sizeof(NMS) * t->cap); }
  if (!t->s || (t->n + 1) * 2 > t->cap) {
    size_t oc = t->cap; NMS *os = t->s; t->cap = oc ? oc * 2 : 64; t->s = (NMS *)calloc(t->cap, sizeof(NMS)); t->n = 0;
    for (size_t i = 0; i < oc; i++) if (os[i].ep == nat_epoch) nmt_put(t, os[i].key, os[i].st, os[i].iv, os[i].tv);
    free(os);
  }
  size_t i = nmt_h(k, t->cap); while (t->s[i].ep == nat_epoch && t->s[i].key != k) i = (i + 1) & (t->cap - 1);
  if (t->s[i].ep != nat_epoch) t->n++;
  t->s[i].key = k; t->s[i].ep = nat_epoch; t->s[i].st = st; t->s[i].iv = iv; t->s[i].tv = tv;
}
`;
  // The hand-written C of the benchmark algorithms (as bench/reference.c), for queries that run one of them:
  // the program times it too and prints this program's speed as a % of C's.  Lists are cells from a bump
  // heap, reset before each run, as in bench/reference.c.
  const REF_C = `
/* ---------- hand-written C reference (bench/reference.c) ---------- */
typedef struct ref_cell { long head; struct ref_cell *tail; } ref_cell;
static ref_cell *ref_heap; static size_t ref_hp, ref_hcap;
static volatile long ref_sink;
static void ref_need(size_t n) { if (n > ref_hcap) { free(ref_heap); ref_hcap = n; ref_heap = (ref_cell *)malloc(n * sizeof(ref_cell)); if (!ref_heap) dl_die("out of memory", NULL); } }
static ref_cell *ref_cons(long h, ref_cell *t) { ref_cell *c = &ref_heap[ref_hp++]; c->head = h; c->tail = t; return c; }
static long ref_fib(long n) { if (n == 0) return 0; if (n == 1) return 1; return ref_fib(n - 1) + ref_fib(n - 2); }
static ref_cell *ref_app(ref_cell *a, ref_cell *l) { if (!a) return l; return ref_cons(a->head, ref_app(a->tail, l)); }
static ref_cell *ref_nrev(ref_cell *l) { if (!l) return NULL; return ref_app(ref_nrev(l->tail), ref_cons(l->head, NULL)); }
static ref_cell *ref_numlist(long lo, long hi) { ref_cell *r = NULL; for (long i = hi; i >= lo; i--) r = ref_cons(i, r); return r; }
static ref_cell *ref_doubles(ref_cell *l) { if (!l) return NULL; return ref_cons(2 * l->head, ref_doubles(l->tail)); }
static long ref_total(ref_cell *l) { long s = 0; for (; l; l = l->tail) s += l->head; return s; }
static int ref_no_attack(long q, const long *qs, int n, long d) { for (int i = 0; i < n; i++, d++) if (q == qs[i] + d || q == qs[i] - d) return 0; return 1; }
static int ref_safe(const long *qs, int n) { for (int i = 0; i < n; i++) if (!ref_no_attack(qs[i], qs + i + 1, n - i - 1, 1)) return 0; return 1; }
static long ref_sols; static long ref_solbuf[64][16];
static void ref_perm(long *rest, int nrest, long *out, int k, int n) {
  if (nrest == 0) { if (ref_safe(out, n)) { for (int i = 0; i < n; i++) ref_solbuf[ref_sols & 63][i] = out[i]; ref_sols++; } return; }
  for (int i = 0; i < nrest; i++) { long x = rest[i], tmp[16]; int m = 0; for (int j = 0; j < nrest; j++) if (j != i) tmp[m++] = rest[j]; out[k] = x; ref_perm(tmp, m, out, k + 1, n); }
}
static long ref_queens(int n) { long ns[16], out[16]; for (int i = 0; i < n; i++) ns[i] = i + 1; ref_sols = 0; ref_perm(ns, n, out, 0, n); return ref_sols; }
static long ref_pin(void) { long n = 0, acc = 0; for (long a = 0; a <= 9; a++) for (long b = 0; b <= 9; b++) for (long c = 0; c <= 9; c++) if (a + b + c == 25) { n++; acc += a * 100 + b * 10 + c; } ref_sink = acc; return n; }
static const int ref_par[][2] = { {0, 1}, {1, 2}, {2, 3} };
static int ref_ancs[16], ref_nanc;
static int ref_anc_bb(int z, int y) { int n = 0; for (int i = 0; i < 3; i++) if (ref_par[i][0] == z && ref_par[i][1] == y) n++; for (int i = 0; i < 3; i++) if (ref_par[i][0] == z) n += ref_anc_bb(ref_par[i][1], y); return n; }
static void ref_anc(int y) { for (int i = 0; i < 3; i++) if (ref_par[i][1] == y) ref_ancs[ref_nanc++] = ref_par[i][0]; for (int i = 0; i < 3; i++) for (int k = ref_anc_bb(ref_par[i][1], y); k > 0; k--) ref_ancs[ref_nanc++] = ref_par[i][0]; }
/* ms per run of a batch loop: batches grow until one takes 20 ms; then the median of 3 batches */
static double ref_ms(void (*run)(long)) {
  long n = 1; double t;
  for (;;) { double t0 = now_ms(); run(n); t = now_ms() - t0; if (t >= 20 || n >= (1L << 30)) break; n = t < 1 ? n * 16 : (long)(n * 24 / t) + 1; }
  double ts[3]; for (int b = 0; b < 3; b++) { double t0 = now_ms(); run(n); ts[b] = (now_ms() - t0) / n; }
  if (ts[0] > ts[1]) { double x = ts[0]; ts[0] = ts[1]; ts[1] = x; } if (ts[1] > ts[2]) { double x = ts[1]; ts[1] = ts[2]; ts[2] = x; } if (ts[0] > ts[1]) { double x = ts[0]; ts[0] = ts[1]; ts[1] = x; }
  return ts[1];
}
`;
  // one run of the hand-written algorithm, and the heap cells it needs
  const refBody = r => ({
    fib: ['ref_sink = ref_fib(' + r.n + ');', 0],
    nrev: ['ref_sink = ref_nrev(ref_numlist(1, ' + r.n + '))->head;', r.n * 2 + r.n * (r.n + 1) / 2 + 16],
    doubles: ['ref_sink = ref_total(ref_doubles(ref_numlist(1, ' + r.n + ')));', r.n * 2 + 16],
    queens: ['ref_sink = ref_queens(' + r.n + ');', 0],
    pin: ['ref_sink = ref_pin();', 0],
    anc: ['ref_nanc = 0; ref_anc(3); ref_sink = ref_nanc;', 0],
  })[r.alg];
  function toC(detlogText, opts) {
    opts = opts || {};
    const prog = P.loadProgram(detlogText);
    // the original Prolog (opts.source), for the algebra that reads predicates as they were written
    let srcProg = null; try { srcProg = opts.source ? P.loadProgram(opts.source) : null; } catch (e) { srcProg = null; }
    const proofNotes = [];
    const warnings = []; const warned = new Set();
    const warn = m => { if (!warned.has(m)) { warned.add(m); warnings.push(m); } };
    const atoms = new Map(), fns = new Map();
    const atomIx = n => { if (!atoms.has(n)) atoms.set(n, atoms.size); return 'AT[' + atoms.get(n) + ']'; };
    const fnIx = n => { if (!fns.has(n)) fns.set(n, fns.size); return 'FN[' + fns.get(n) + ']'; };
    const pfn = k => 'p_' + mangle(k.replace('/', '_'));
    let uid = 0;
    const defs = [], protos = [];

    // a ground compound term is built once, at startup (KC table), and shared: unification never
    // writes into a term without variables, so every call may use the same cells
    const groundT = t => { t = D(t); if (t.t === 'v') return false; if (t.t === 'c') { for (const a of t.a) if (!groundT(a)) return false; } return true; };
    function termC(t, vm, top = true) {
      t = D(t);
      if (top && t.t === 'c' && !opts.noHoist && groundT(t)) return KC(t);
      switch (t.t) {
        case 'v': { if (!t.name || t.name === '_') return 'mk_var()'; const v = vm.get(t); if (!v) throw new Error('unknown variable ' + t.name); return v; }
        case 'n': return t.f ? 'mk_flt(' + (Number.isFinite(t.v) ? String(t.v) + (/[.e]/i.test(String(t.v)) ? '' : '.0') : (t.v > 0 ? 'INFINITY' : t.v < 0 ? '-INFINITY' : 'NAN')) + ')' : 'mk_int(' + t.v + 'LL)';
        case 'a': return atomIx(t.n);
        case 's': return 'mk_str(' + cstrBytes(t.v) + ')';
        case 'c': {
          if (t.f === '.' && t.a.length === 2) {
            const items = []; let x = t;
            while (x.t === 'c' && x.f === '.' && x.a.length === 2) { items.push(termC(x.a[0], vm, top)); x = D(x.a[1]); }
            return 'mk_list(' + items.length + ', (Term*[]){' + items.join(', ') + '}, ' + termC(x, vm) + ')';
          }
          return 'mk_cmp(' + fnIx(t.f) + ', ' + t.a.length + ', (Term*[]){' + t.a.map(x => termC(x, vm, top)).join(', ') + '})';
        }
      }
      throw new Error('bad term');
    }
    function argsC(as, vm) { return as.length ? '(Term*[]){' + as.map(x => termC(x, vm)).join(', ') + '}' : 'NULL'; }
    // generate-and-test fusion, as in the JIT (detlog_fast.js fuseGenLoop):
    //   builtin_rows(G, P), splice_extend(P, [G], e(Env), R2), loop(R2, R1)
    // with G member/2 or permutation/2 over a proper list and loop a packet loop (no cut) whose row predicate
    // starts by copying its row.  Each solution is bound in place; a DET filter row predicate runs through the
    // native entry and only kept rows are copied; otherwise the row predicate runs and its rows are copied.
    const isCT = (t, f, n) => { t = D(t); return t.t === 'c' && t.f === f && t.a.length === n; };
    function fusionPlan(g1, g2, g3, rest) {
      if (P.key(g1) !== 'builtin_rows/2' || P.key(g2) !== 'splice_extend/4' || !P.loopShape) return null;
      const G = D(g1.a[0]), Pv = D(g1.a[1]), gk = P.key(G);
      if ((gk !== 'member/2' && gk !== 'permutation/2') || Pv.t !== 'v' || D(g2.a[0]) !== Pv) return null;
      const pat = P.listToArray(g2.a[1]); if (!pat || pat.length !== 1 || P.show(pat[0]) !== P.show(G)) return null;
      const R2 = D(g2.a[3]); if (R2.t !== 'v' || !g3.a || g3.a.length !== 2 || D(g3.a[0]) !== R2) return null;
      const k3 = P.key(g3); const lcls = prog.preds.get(k3); if (!lcls) return null;
      const sh = P.loopShape(k3, lcls); if (!sh || sh.cutVariant || !prog.preds.has(sh.callKey)) return null;
      const rcl = prog.preds.get(sh.callKey).find(c => isCT(D(c.head).a[0], 'e', 1));
      if (!rcl) return null;
      const rb = P.flatConj(rcl.body).map(D);
      if (P.key(rb[0]) !== 'copy_term/2' || D(rb[0].a[0]) !== D(D(D(rcl.head).a[0]).a[0])) return null;
      if (rest.concat([g3.a[1]]).some(x => P.termVars(x).some(v => v === Pv || v === R2)) || P.termVars(g2.a[2]).includes(R2)) return null;
      const env = g2.a[2]; if (!isCT(env, 'e', 1)) return null;
      let filt = null;
      const Lr = P.listToArray(rb[0].a[1]), Ev = P.listToArray(D(env).a[0]), ic = rb[1];
      if (rb.length === 2 && Lr && Ev && Lr.length === Ev.length && Lr.every(v => D(v).t === 'v') && P.key(ic) === 'if_commit/3') {
        const c = P.flatConj(ic.a[0]).map(D), th = D(ic.a[1]);
        if (c.length === 2 && c[0].t === 'c' && /__d$/.test(c[0].f) && P.key(c[1]) === '\\==/2' && D(c[1].a[0]) === D(c[0].a[c[0].a.length - 1]) && P.key(th) === 'if_commit/3') {
          const Sv = D(c[0].a[c[0].a.length - 1]), yes = D(th.a[0]), keep = D(th.a[1]), drop = D(th.a[2]), Orow = D(D(rcl.head).a[1]);
          const okYes = P.key(yes) === '=/2' && D(yes.a[0]) === Sv && D(yes.a[1]).t === 'a' && D(yes.a[1]).n === 'yes';
          const okKeep = P.key(keep) === '=/2' && D(keep.a[0]) === Orow && P.show(keep.a[1]) === P.show(P.list([P.Cmp('e', [P.list(Lr)])]));
          const okDrop = P.key(drop) === '=/2' && D(drop.a[0]) === Orow && D(drop.a[1]).t === 'a' && D(drop.a[1]).n === '[]';
          const sub = new Map(Lr.map((v, i) => [D(v), Ev[i]]));
          const subst = t => { t = D(t); if (t.t === 'v') return sub.has(t) ? sub.get(t) : null; if (t.t === 'c') { const a = t.a.map(subst); return a.includes(null) ? null : P.Cmp(t.f, a); } return t; };
          const args = c[0].a.slice(0, -1).map(subst);
          if (okYes && okKeep && okDrop && !args.includes(null) && natModes.has(P.key(c[0]))) filt = { k: P.key(c[0]), args };
        }
      }
      return { gk, G, env, out: g3.a[1], rowKey: sh.callKey, filt };
    }
    function fusedC(pl, generic, vm, fail, ind) {
      const n = ++uid, list = pl.gk === 'member/2' ? pl.G.a[1] : pl.G.a[0], x = pl.gk === 'member/2' ? pl.G.a[0] : pl.G.a[1];
      const body = y => 'size_t m = TR_TOP; if (unify(x' + n + ', ' + y + ')) { STEP(); STEP(); STEP(); STEP(); if (++nrow' + n + ' > 1000000) dl_die("builtin_rows: infinite generator", NULL);\n' +
        (pl.filt ? '  Term *Sv = mk_var(); Term **fa = (Term*[]){' + pl.filt.args.map(a => termC(a, vm)).concat(['Sv']).join(', ') + '};\n  if (' + natEntryFn(pl.filt.k) + '(fa)) { if (deref(Sv) == ' + atomIx('yes') + ') tv_push(&res' + n + ', copy_term(ev' + n + ')); }\n  else ' : '  ') +
        '{ Term *Ov = mk_var(); if (!' + pfn(pl.rowKey) + '((Term*[]){ ev' + n + ', Ov })) ok' + n + ' = 0; else { TV o1 = { 0 }; list_to_tv(Ov, &o1); for (size_t j = 0; j < o1.n; j++) tv_push(&res' + n + ', copy_term(o1.v[j])); tv_free(o1.v); } }\n' +
        '} undo(m);';
      let loop;
      // permutation(Xs, Ys) tested by a native DET predicate on Ys alone, with no outputs: each permutation
      // is written into the same k list cells (the test is pure and keeps nothing), the native function is
      // called directly in its 'i' mode, and only a kept permutation is built as a new list and copied.
      // permutation(Xs, Ys) tested by a pairwise test (src/algebra.js): each element is tested against those
      // already placed and a failing prefix is dropped; the lists kept are the same, in the same order.
      const pw = pl.filt && pl.gk === 'permutation/2' && srcProg && pl.filt.args.length === 1 && D(pl.filt.args[0]) === D(x) && /__d\/\d+$/.test(pl.filt.k) ? P.pairwise(srcProg, pl.filt.k.replace(/__d\/(\d+)$/, (_, a) => '/' + (+a - 1))) : null;
      if (pw) {
        proofNotes.push(pw.proof);
        const keep = 'Term *y = tv_list(&cur); size_t m = TR_TOP; if (unify(x' + n + ', y)) tv_push(&res' + n + ', copy_term(ev' + n + ')); undo(m);';
        const test = pw.code('p', 'yv', 'dist', false);
        loop = '{ size_t k = xs' + n + '.n; int allint = 1; for (size_t i = 0; i < k; i++) if (deref(xs' + n + '.v[i])->tag != T_INT) allint = 0;\n' +
          '  if (!allint) dl_die("pairwise generate-and-test needs a list of integers", NULL);\n' +
          '  long long *val = (long long *)malloc(sizeof(long long) * (k + 1)), *pl = (long long *)malloc(sizeof(long long) * (k + 1)); for (size_t i = 0; i < k; i++) val[i] = deref(xs' + n + '.v[i])->iv;\n' +
          '  size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; TV cur = { 0 };\n' +
          '  for (; ok' + n + ';) {\n' +
          '    if ((size_t)d == k) { ' + keep + '\n      d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    while (idx[d] < k && used[idx[d]]) idx[d]++;\n' +
          '    if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    { long long yv = val[idx[d]]; int okp = 1; for (long i = d - 1; i >= 0; i--) { long long p = pl[i], dist = ' + pw.c0 + ' + (d - 1 - i); if (!(' + test + ')) { okp = 0; break; } } if (!okp) { idx[d]++; continue; } }\n' +
          '    used[idx[d]] = 1; pl[d] = val[idx[d]]; tv_push(&cur, xs' + n + '.v[idx[d]]); d++; idx[d] = 0;\n  }\n  free(idx); free(used); tv_free(cur.v); free(val); free(pl); }\n';
      } else {
      const md = pl.filt && pl.gk === 'permutation/2' && pl.filt.args.length === 1 && D(pl.filt.args[0]) === D(x) && (natModes.get(pl.filt.k) || []).find(m => m.mode === 'i');
      if (md) {
        const keep = 'Term *y = tv_list(&cur); size_t m = TR_TOP; if (unify(x' + n + ', y)) tv_push(&res' + n + ', copy_term(ev' + n + ')); undo(m);';
        loop = '{ size_t k = xs' + n + '.n; size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; TV cur = { 0 };\n' +
          '  Term **cell = (Term **)malloc(sizeof(Term *) * (k + 1)); for (size_t i = 0; i < k; i++) cell[i] = mk_cons(NIL, NIL), cell[i]->cpe = 0; /* the cells are reused: not ground-marked */ for (size_t i = 0; i + 1 < k; i++) cell[i]->args[1] = cell[i + 1]; cell[k] = NIL;\n' +
          '  for (; ok' + n + ';) {\n' +
          '    if ((size_t)d == k) {\n' +
          '      for (size_t i = 0; i < k; i++) cell[i]->args[0] = cur.v[i];\n' +
          '      if (++nrow' + n + ' > 1000000) dl_die("builtin_rows: infinite generator", NULL);\n' +
          '      int r; { nat_jmp jb; nat_jmp *sv = nat_jb; nat_jb = &jb; nat_epoch++; if (NAT_SETJMP(jb)) { nat_jb = sv; r = 2; } else { r = ' + md.name + '(cell[0]); nat_jb = sv; } }\n' +
          '      if (r == 1) { ' + keep + ' }\n' +
          '      else if (r == 2) { Term *y = tv_list(&cur); { ' + body('y') + ' } }\n' +
          '      d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    while (idx[d] < k && used[idx[d]]) idx[d]++;\n' +
          '    if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    used[idx[d]] = 1; tv_push(&cur, xs' + n + '.v[idx[d]]); d++; idx[d] = 0;\n  }\n  free(idx); free(used); tv_free(cur.v); free(cell); }\n';
      } else if (pl.gk === 'member/2') loop = 'for (size_t i = 0; i < xs' + n + '.n && ok' + n + '; i++) { ' + body('xs' + n + '.v[i]') + ' }\n';
      else loop = '{ size_t k = xs' + n + '.n; size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; TV cur = { 0 };\n' +
        '  for (; ok' + n + ';) {\n' +
        '    if ((size_t)d == k) { Term *y = tv_list(&cur); { ' + body('y') + ' } d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
        '    while (idx[d] < k && used[idx[d]]) idx[d]++;\n' +
        '    if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
        '    used[idx[d]] = 1; tv_push(&cur, xs' + n + '.v[idx[d]]); d++; idx[d] = 0;\n  }\n  free(idx); free(used); tv_free(cur.v); }\n';
      }
      return ind + '{ TV xs' + n + ' = { 0 };\n' + ind + 'if (!list_to_tv(' + termC(list, vm) + ', &xs' + n + ')) {\n' + ind + 'tv_free(xs' + n + '.v);\n' + generic + ind + '} else {\n' +
        ind + 'Term *x' + n + ' = ' + termC(x, vm) + ', *ev' + n + ' = ' + termC(pl.env, vm) + '; TV res' + n + ' = { 0 }; size_t nrow' + n + ' = 0; int ok' + n + ' = 1; STEP(); STEP(); STEP();\n' +
        loop + ind + 'tv_free(xs' + n + '.v);\n' + ind + 'if (!ok' + n + ') { tv_free(res' + n + '.v); ' + fail + ' }\n' +
        ind + '{ Term *rl = tv_list(&res' + n + '); tv_free(res' + n + '.v); if (!unify(' + termC(pl.out, vm) + ', rl)) ' + fail + ' } } }\n';
    }
    function stmt(g, vm, fail, ind) {
      g = D(g); const k = P.key(g); const as = g.t === 'c' ? g.a : [];
      if (g.t === 'v') throw new Error('variable goal');
      if (k === ',/2') {
        const gs = P.flatConj(g).map(D); let code = '';
        for (let i = 0; i < gs.length; i++) {
          const pl = i + 2 < gs.length && fusionPlan(gs[i], gs[i + 1], gs[i + 2], gs.slice(i + 3));
          if (pl) { code += fusedC(pl, stmt(gs[i], vm, fail, ind) + stmt(gs[i + 1], vm, fail, ind) + stmt(gs[i + 2], vm, fail, ind), vm, fail, ind); i += 2; continue; }
          code += stmt(gs[i], vm, fail, ind);
        }
        return code;
      }
      switch (k) {
        case 'true/0': return '';
        case 'fail/0': case 'false/0': return ind + fail + '\n';
        case 'if_commit/3': {
          const n = ++uid;
          return ind + '{ size_t m' + n + ' = TR_TOP; int ok' + n + ' = 1; dl_decisions++;\n' +
            ind + '  do {\n' + stmt(g.a[0], vm, '{ ok' + n + ' = 0; break; }', ind + '    ') + ind + '  } while (0);\n' +
            ind + '  if (ok' + n + ') {\n' + stmt(g.a[1], vm, fail, ind + '    ') + ind + '  } else {\n' + ind + '    undo(m' + n + ');\n' + stmt(g.a[2], vm, fail, ind + '    ') + ind + '  }\n' + ind + '}\n';
        }
        case 'detlog_unsupported/2': warn('predicate ' + show(g.a[0]) + ' was not converted; calling it stops the C program');
          return ind + 'rt_unsupported(' + cstrBytes(show(g.a[0])) + ');\n';
      }
      if (RT[k]) {
        if (k === 'builtin_rows/2') { const bk = P.key(g.a[0]); if (!C_ROWS.has(bk)) warn('builtin_rows for ' + bk + ' is not in the C runtime'); }
        if (k === 'effect_text/2') { const bk = P.key(g.a[0]); if (!C_EFFECTS.has(bk)) warn('output builtin ' + bk + ' is not in the C runtime'); }
        return ind + 'if (!' + RT[k] + '(' + as.map(x => termC(x, vm)).join(', ') + ')) ' + fail + '\n';
      }
      if (prog.preds.has(k)) {
        if (natModes.has(k) && /__d$/.test(g.f) && !/__d$/.test(curPred)) return ind + '{ Term **na = ' + (as.length ? argsC(as, vm) : 'NULL') + '; if (!' + natEntryFn(k) + '(na) && !' + pfn(k) + '(na)) ' + fail + ' }\n';
        return ind + 'if (!' + pfn(k) + '(' + argsC(as, vm) + ')) ' + fail + '\n';
      }
      if (!C_BUILTINS.has(k)) warn('builtin ' + k + ' is not in the C runtime');
      // the common type tests and unifications are written in place (no dispatch by name); checked builds keep
      // bi_call, which counts steps
      if (!opts.checked) {
        const A = () => termC(as[0], vm), B = () => termC(as[1], vm);
        switch (k) {
          case '=/2': return ind + 'if (!unify(' + A() + ', ' + B() + ')) ' + fail + '\n';
          case 'var/1': return ind + 'if (deref(' + A() + ')->tag != T_VAR) ' + fail + '\n';
          case 'nonvar/1': return ind + 'if (deref(' + A() + ')->tag == T_VAR) ' + fail + '\n';
          case '==/2': return ind + 'if (compare(' + A() + ', ' + B() + ') != 0) ' + fail + '\n';
          case '\\==/2': return ind + 'if (compare(' + A() + ', ' + B() + ') == 0) ' + fail + '\n';
          case 'copy_term/2': return ind + 'if (!unify(' + B() + ', copy_term(' + A() + '))) ' + fail + '\n';
        }
      }
      return ind + 'if (!bi_call(' + cstrBytes(k) + ', ' + argsC(as, vm) + ')) ' + fail + '\n';
    }
    function headInfo(t) {
      t = D(t);
      if (t.t === 'v') return '-1, NULL, 0, 0';
      if (t.t === 'a') return 'T_ATOM, ' + atomIx(t.n) + '->name, 0, 0';
      if (t.t === 'n') return t.f ? 'T_FLT, NULL, 0, 0' : 'T_INT, NULL, 0, ' + t.v + 'LL';
      if (t.t === 's') return 'T_STR, NULL, 0, 0';
      return 'T_CMP, ' + fnIx(t.f) + ', ' + t.a.length + ', 0';
    }
    // ---------- native tier (src/native.js) for the modes the program's queries use ----------
    // The JS engine runs the queries once (a profile); every (predicate, mode) its native tier compiled is
    // compiled here too, to C: long long for integers, outputs through pointers, longjmp to bail out.
    let nativeModes = opts.nativeModes;
    if (!nativeModes && opts.native !== false && P.runDetlogFast && P.nativeModesOf && P.DETLOG_NATIVE !== false) {
      const np = P.loadProgram(detlogText);
      for (const q of opts.queries || []) { try { P.runDetlogFast(np, q.pred, q.vars, { stepLimit: opts.profileSteps || 2e7 }); } catch (e) { /* the profile only gathers modes */ } }
      nativeModes = P.nativeModesOf(np);
    }
    const kcs = [], kcIx = new Map();
    const KC = t => { const key = P.show(t, { quoted: true }) + '|' + (t.t === 'n' ? (t.f ? 'f' : 'i') : t.t); if (!kcIx.has(key)) { kcIx.set(key, kcs.length); kcs.push(t); } return 'KC[' + kcIx.get(key) + ']'; };
    const nTables = new Map();
    const sigs = new Map();
    const cname = (name, int) => name + (int ? '_i' : '_t');
    const EMC = {
      YES: '1', NO: '0', MAYBE: '2', EQOP: '==', NEOP: '!=', BAIL: 'nat_bail();',
      v: (name, int) => cname(name, int),
      num: v => v + 'LL',
      k: t => t.t === 'a' ? atomIx(t.n) : KC(t),
      box: e => 'mk_int(' + e + ')',
      unbox: e => 'n_iv(' + e + ')',
      cmp: (f, args) => f === '.' && args.length === 2 ? (opts.checked ? 'mk_cons(' : 'mk_gcons(') + args[0] + ', ' + args[1] + ')' : 'mk_cmp(' + fnIx(f) + ', ' + args.length + ', (Term*[]){' + args.join(', ') + '})',
      eq: (a, b) => 'n_eq(' + a + ', ' + b + ')',
      isIntVal: (e, v) => 'n_isv(' + e + ', ' + v + ')',
      tmp: (t, e) => 'Term *' + t + ' = deref(' + e + ');',
      isCmp: (t, f, n) => t + '->tag == T_CMP && ' + t + '->name == ' + (f === '.' ? 'A_DOT->name' : fnIx(f)) + ' && ' + t + '->arity == ' + n,
      arg: (t, i) => t + '->args[' + i + ']',
      keyTest: (pat, t) => {
        if (pat.t === 'a') return t + ' == ' + atomIx(pat.n);
        if (pat.t === 'n') return pat.f ? t + '->tag == T_FLT && ' + t + '->fv == ' + (Number.isFinite(pat.v) ? String(pat.v) + (/[.e]/i.test(String(pat.v)) ? '' : '.0') : (pat.v > 0 ? 'INFINITY' : pat.v < 0 ? '-INFINITY' : 'NAN')) : t + '->tag == T_INT && ' + t + '->iv == ' + pat.v + 'LL';
        if (pat.t === 's') return t + '->tag == T_STR && !strcmp(' + t + '->name, ' + cstrBytes(pat.v) + ')';
        return '0';
      },
      fn: (name, args) => ({ IDIV: 'n_idiv', IMOD: 'n_imod', IREM: 'n_irem', MIN: 'n_min', MAX: 'n_max', ABS: 'llabs', IADD: 'n_iadd', ISUB: 'n_isub', IMUL: 'n_imul' })[name] + '(' + args.join(', ') + ')',
      assign: (lhs, rhs) => lhs + ' = ' + rhs + ';\n',
      fail: L => 'goto ' + L + ';',
      blockNoThen: (L, rc, re) => '{\n' + rc + '}\n' + L + ': ;\n' + re,
      block: (L, ok, rc, rt, re) => '{ int ' + ok + ' = 0;\n{\n' + rc + ok + ' = 1;\n}\n' + L + ': ;\nif (' + ok + ') {\n' + rt + '} else {\n' + re + '}\n}\n',
      retOuts: vals => vals.map((v, i) => '*o' + i + ' = ' + v + ';').join(' ') + ' return 1;',
      retStatus: v => 'return ' + v + ';',
      call: (callee, ins, outs, retInt, rs, memo) => {
        const args = ins.concat(outs.map(o => '&' + o)).join(', ');
        // memoised in a table keyed by the one integer input
        if (memo && /^n?o?$/.test(memo.mode) && memo.mode.startsWith('n') && ins.length === 1 && outs.length <= 1) {
          if (!nTables.has(memo.table)) nTables.set(memo.table, 'NT' + nTables.size);
          const T = nTables.get(memo.table), fld = retInt ? 'iv' : 'tv';
          const fill = outs.length ? 'if (' + rs + ' == 1) ' + outs[0] + ' = ms->' + fld + ';' : '';
          return '{ NMS *ms = nmt_get(&' + T + ', ' + ins[0] + '); if (ms) { ' + rs + ' = ms->st; ' + fill + ' } else { ' + rs + ' = ' + callee + '(' + args + '); nmt_put(&' + T + ', ' + ins[0] + ', ' + rs + ', ' + (outs.length && retInt ? '(' + rs + ' == 1 ? ' + outs[0] + ' : 0)' : '0') + ', ' + (outs.length && !retInt ? '(' + rs + ' == 1 ? ' + outs[0] + ' : NULL)' : 'NULL') + '); } }\n';
        }
        return rs + ' = ' + callee + '(' + args + ');\n';
      },
      func: (name, params, nOuts, selfInt, used, statusLocals, body) => {
        const ps = params.map(p => (p.int ? 'long long ' : 'Term *') + cname(p.name, p.int));
        for (let i = 0; i < nOuts; i++) ps.push((nOuts === 1 && selfInt ? 'long long *' : 'Term **') + 'o' + i);
        const sig = 'static int ' + name + '(' + (ps.length ? ps.join(', ') : 'void') + ')';
        sigs.set(name, sig);
        const decl = used.map(u => (u.int ? 'long long ' : 'Term *') + cname(u.name, u.int) + (u.int ? ' = 0;' : ' = NULL;')).join(' ') + (statusLocals.length ? ' int ' + statusLocals.map(x => x + ' = 0').join(', ') + ';' : '');
        return sig + ' {\n  STEP();\n  ' + decl + '\n' + body + '  nat_bail(); return 0;\n}\n';
      },
    };
    // Last calls in the native tier (unchecked), so that list recursions run as loops:
    //  1. s = f(A, &v); if (s != 1) return s; *o = v; return 1;      ==>  return f(A, o);
    //     (f's result code is passed on unchanged and *o is read only after success)
    //  2. s = f(A, &v); if (s != 1) return s; *o = cons(H, v); return 1;  ==>  c = cons(H, NULL); *o = c; return f(A, &c->args[1]);
    //     (destination passing: H does not mention v, so it may be built first; on failure the caller ignores *o)
    // f must be the function itself, so the call is a self tail call that the C compiler turns into a jump.
    function lastCalls(src) {
      const m = /^static int (nat\d+)\(/m.exec(src); if (!m) return src;
      const f = m[1];
      const esc = x => x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      const splitArgs = t => { const out = []; let d = 0, cur = ''; for (const ch of t) { if (ch === '(') d++; if (ch === ')') d--; if (ch === ',' && d === 0) { out.push(cur.trim()); cur = ''; } else cur += ch; } if (cur.trim()) out.push(cur.trim()); return out; };
      const re = new RegExp('\\{ (s\\d+) = ' + esc(f) + '\\((.*)\\);\\nif \\(\\1 != 1\\) return \\1;\\n((?:\\*o\\d+ = [^;]*; )+)return 1; \\}', 'g');
      return src.replace(re, (all, sv, argText, asg) => {
        const args = splitArgs(argText);
        const outs = []; while (args.length && /^&v\d+_[a-z]$/.test(args[args.length - 1])) outs.unshift(args.pop().slice(1));
        if (!outs.length) return all;
        const assigns = [...asg.matchAll(/\*(o\d+) = ([^;]*); /g)].map(x => ({ o: x[1], e: x[2] }));
        if (assigns.length !== outs.length) return all;
        const mentions = (e, v) => new RegExp('\\b' + v + '\\b').test(e);
        const pre = [], slot = [];
        for (const v of outs) {
          const as = assigns.filter(x => mentions(x.e, v)); if (as.length !== 1) return all;
          const { o, e } = as[0];
          if (e === v) { slot.push(o); continue; }
          const c = /^mk_gcons\((.*), (v\d+_t)\)$/.exec(e);
          if (!c || c[2] !== v || outs.some(w => mentions(c[1], w))) return all;
          const cv = 'c' + pre.length + '_';
          pre.push('Term *' + cv + ' = mk_gcons(' + c[1] + ', NULL); *' + o + ' = ' + cv + ';');
          slot.push('&' + cv + '->args[1]');
        }
        return '{ ' + pre.join(' ') + (pre.length ? ' ' : '') + 'return ' + f + '(' + args.concat(slot).join(', ') + '); }';
      });
    }
    const nDone = new Map(); const nDefs = []; let nSeq = 0;
    const natModes = new Map(); // predicate key -> [{ mode, name, retInt }]
    for (const km of nativeModes || []) {
      const i = km.lastIndexOf('|'); const k = km.slice(0, i), mode = km.slice(i + 1);
      if (nDone.has(km) || !prog.preds.has(k)) continue;
      const batch = P.nativeBatch(prog, k, mode, EMC, { has: x => nDone.has(x), get: x => nDone.get(x) }, () => 'nat' + (nSeq++));
      if (!batch) { nDone.set(km, null); warn('native function for ' + km + ' not compiled to C'); continue; }
      for (const [key2, e] of batch) { nDone.set(key2, { ref: e.name, retInt: e.retInt }); nDefs.push(opts.checked ? e.src : lastCalls(e.src)); }
    }
    for (const km of nativeModes || []) {
      const f = nDone.get(km); if (!f) continue;
      const i = km.lastIndexOf('|'); const k = km.slice(0, i);
      if (!natModes.has(k)) natModes.set(k, []);
      natModes.get(k).push({ mode: km.slice(i + 1), name: f.ref, retInt: f.retInt });
    }
    // entry from packet code: the argument modes decide; a compiled mode runs natively, otherwise p__d runs
    const natEntryFn = k => 'nat_' + pfn(k);
    const natEntries = [];
    for (const [k, ms] of natModes) {
      const n = +k.slice(k.lastIndexOf('/') + 1) - 1;
      let c = 'static int ' + natEntryFn(k) + '(Term **a) {\n  Term *x[' + Math.max(1, n) + ']; char m[' + (n + 1) + '];\n';
      c += '  for (int i = 0; i < ' + n + '; i++) { x[i] = deref(a[i]); if (x[i]->tag == T_VAR) { for (int j = 0; j < i; j++) if (x[j] == x[i]) return 0; m[i] = \'o\'; } else if (x[i]->tag == T_INT) m[i] = \'n\'; else if (DL_GROUND(x[i])) m[i] = \'i\'; else return 0; }\n';
      c += '  m[' + n + '] = 0; Term *S = deref(a[' + n + ']); if (S->tag != T_VAR) return 0; for (int i = 0; i < ' + n + '; i++) if (x[i] == S) return 0;\n';
      for (const md of ms) {
        const outs = [...md.mode].map((ch, i) => ch === 'o' ? i : -1).filter(i => i >= 0);
        const ins = [...md.mode].map((ch, i) => ch === 'n' ? 'x[' + i + ']->iv' : ch === 'i' ? 'x[' + i + ']' : null).filter(Boolean);
        const intOut = outs.length === 1 && md.retInt;
        c += '  if (!strcmp(m, "' + md.mode + '")) {\n    ' + outs.map((o, j) => (intOut ? 'long long' : 'Term *') + ' o' + j + ' = 0;').join(' ') + '\n';
        c += '    nat_jmp jb; nat_jmp *sv = nat_jb; nat_jb = &jb; nat_epoch++;\n    if (NAT_SETJMP(jb)) { nat_jb = sv; return 0; }\n';
        c += '    int r = ' + md.name + '(' + ins.concat(outs.map((o, j) => '&o' + j)).join(', ') + ');\n    nat_jb = sv;\n';
        c += '    if (r == 2) return 0;\n    if (r == 0) { bind(S, ' + atomIx('no') + '); return 1; }\n';
        c += '    ' + outs.map((o, j) => 'bind(x[' + o + '], ' + (intOut ? 'mk_int(o' + j + ')' : 'o' + j) + ');').join(' ') + ' bind(S, ' + atomIx('yes') + '); return 1;\n  }\n';
      }
      c += '  return 0;\n}\n';
      natEntries.push(c);
    }
    let curPred = '';

    for (const k of prog.order) {
      curPred = k.slice(0, k.lastIndexOf('/'));
      const cls = prog.preds.get(k); const f = pfn(k);
      protos.push('static int ' + f + '(Term **a);');
      const parts = [];
      cls.forEach((cl, i) => {
        const vm = new Map(); let vi = 0;
        const vs = P.termVars(P.Cmp('-', [cl.head, cl.body])).filter(v => v.name && v.name !== '_');
        for (const v of vs) vm.set(v, 'v' + (++vi));
        const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
        let body = 'static int ' + f + '_c' + (i + 1) + '(Term **a) {\n';
        // a head argument that is a variable not seen in an earlier argument is that argument itself:
        // no fresh variable to make and bind (unchecked and checked alike: unify would only bind it)
        const alias = new Map(), seen = new Set();
        hargs.forEach((h, j) => { const d = D(h); if (d.t === 'v' && d.name && d.name !== '_' && !seen.has(d) && !alias.has(d)) alias.set(d, j); for (const v of P.termVars(h)) seen.add(v); });
        if (vs.length) body += '  Term ' + vs.map(v => '*' + vm.get(v) + ' = ' + (alias.has(v) ? 'a[' + alias.get(v) + ']' : 'mk_var()')).join(', ') + ';\n';
        body += '  (void)a;\n';
        hargs.forEach((h, j) => { const d = D(h); if (d.t === 'v' && alias.get(d) === j) return; body += '  if (!unify(a[' + j + '], ' + termC(h, vm) + ')) return 0;\n'; });
        body += stmt(cl.body, vm, 'return -1;', '  ');
        body += '  return 1;\n}\n';
        defs.push(body);
        parts.push({ i, info: hargs.length ? headInfo(hargs[0]) : '-1, NULL, 0, 0' });
      });
      let disp = 'static int ' + f + '(Term **a) {\n  STEP(); size_t m = TR_TOP; int r; (void)m; (void)r;\n';
      for (const p of parts) {
        const test = (D(cls[0].head).t === 'c') ? 'fa(a[0], ' + p.info + ')' : '1';
        disp += '  if (' + test + ') { r = ' + f + '_c' + (p.i + 1) + '(a); if (r == 1) return 1; undo(m); if (r < 0) return 0; }\n';
      }
      disp += '  return 0;\n}\n';
      defs.push(disp);
    }
    // main
    const qs = (opts.queries || []).filter(q => q.pred && prog.preds.has(q.pred + '__cp/' + (q.vars.length + 1)));
    // queries that run a benchmark algorithm, checked by the hand-written version giving exactly their answers
    const refs = new Map(), refFns = [];
    if (opts.cReference !== false && P.cRefPattern && P.runDetlogFast) {
      let rp = null;
      qs.forEach((q, i) => {
        if (!P.cRefPattern(q.text)) return;
        try {
          rp = rp || P.loadProgram(detlogText);
          const r = P.runDetlogFast(rp, q.pred, q.vars, { stepLimit: 2e7 });
          const ref = !r.error && P.cRefMatch(q.text, r.events);
          if (!ref) return;
          const [body, cells] = refBody(ref);
          refs.set(i, { fn: 'ref_q' + i, alg: ref.alg, cells });
          refFns.push('static void ref_q' + i + '(long reps) { for (long i = 0; i < reps; i++) { ref_hp = 0; ' + body + ' } }');
        } catch (e) { /* no reference for this query */ }
      });
    }
    let main = 'int main(int argc, char **argv) {\n  int reps = 1; if (argc > 2 && !strcmp(argv[1], "-r")) reps = atoi(argv[2]); if (reps < 1) reps = 1;\n  int refs = !(argc > 1 && !strcmp(argv[argc - 1], "--no-ref")); (void)refs; /* --no-ref: skip timing the hand-written C */\n  for (int i = 1; i < argc; i++) { if (!strcmp(argv[i], "--events")) ev_mode = 1; if (!strcmp(argv[i], "--first")) first_only = 1; }\n  double st0 = now_ms(); rt_init(); init_tables(); long lim0 = dl_step_limit;\n  printf("%% startup %.4f ms\\n", now_ms() - st0);\n';
    qs.forEach(q => {
      const k = q.pred + '__cp/' + (q.vars.length + 1);
      main += '  {\n    const char *nm[] = {' + (q.vars.length ? q.vars.map(cstrBytes).join(', ') : '""') + '};\n';
      main += '    Term *qv[' + (q.vars.length + 1) + ']; int ok = 0; long s0 = dl_steps, d0 = dl_decisions; double t0 = now_ms();\n';
      // every repetition but the last runs on memory that is released afterwards (the last one is printed)
      main += '    ArenaMark am = arena_mark(); size_t tm = TR_TOP;\n';
      main += '    for (int rep = 0; rep < reps; rep++) { if (rep) { undo(tm); arena_release(am); } dl_step_limit = dl_steps + lim0; /* the step limit is per run */ for (int i = 0; i < ' + (q.vars.length + 1) + '; i++) qv[i] = mk_var(); memo_clear(); ok = ' + pfn(k) + '(qv); }\n';
      main += '    double t1 = now_ms();\n';
      main += '    if (!ev_mode) printf("?- %s.\\n", ' + cstrBytes(q.text) + ');\n';
      main += '    if (!ok) puts("% query failed (a packet predicate must succeed)"); else { if (ev_mode) putchar(0x1d); print_packet(qv[' + q.vars.length + '], nm, ' + q.vars.length + '); if (ev_mode) putchar(0x1d); }\n';
      main += '    printf("%% steps %ld, decisions %ld, %.4f ms per run\\n", (dl_steps - s0) / reps, (dl_decisions - d0) / reps, (t1 - t0) / reps);\n';
      const ref = refs.get(qs.indexOf(q));
      if (ref) {
        // the same algorithm written by hand in C, timed in this process: this program's speed as a % of C's
        main += '    if (ok && refs) { ref_need(' + Math.max(16, Math.ceil(ref.cells)) + '); double rc = ref_ms(' + ref.fn + '), me = (t1 - t0) / reps;\n';
        main += '      printf("%% hand-written C (' + ref.alg + '): %.6f ms per run; this program runs at %.3g%% of C\'s speed%s\\n", rc, 100 * rc / me, reps < 10 ? " (one timing run: use -r N for a steady figure)" : ""); }\n';
      }
      main += '  }\n';
    });
    main += '  return 0;\n}\n';
    const kcInit = kcs.map((t, i) => '  KC[' + i + '] = ' + termC(t, new Map(), false) + ';').join('\n');
    const atomInit = [...atoms.keys()].map((n, i) => '  AT[' + i + '] = mk_atom(' + cstrBytes(n) + ');').join('\n');
    const fnInit = [...fns.keys()].map((n, i) => '  FN[' + i + '] = intern(' + cstrBytes(n) + ');').join('\n');
    const header = '/* C generated by pl2detlog from Detlog (' + (opts.mode || 'Detlog') + ').\n   Build: cc -O2 -o prog prog.c -lm    Run: ./prog    Time: ./prog -r 1000\n' +
      (proofNotes.length ? '   Algebra (src/algebra.js):\n' + [...new Set(proofNotes)].map(w => '   - ' + w.replace(/\*\//g, '* /')).join('\n') + '\n' : '') +
      (warnings.length ? '   Warnings:\n' + warnings.map(w => '   - ' + w).join('\n') + '\n' : '') + '*/\n';
    const lib = P.C_RUNTIME || '#include "runtime.c"\n';
    const natLib = nDefs.length ? NATIVE_C + [...nTables.values()].map(t => 'static NMT ' + t + ';').join('\n') + '\n' : '';
    const tables = 'static Term *AT[' + Math.max(1, atoms.size) + '];\nstatic const char *FN[' + Math.max(1, fns.size) + '];\nstatic Term *KC[' + Math.max(1, kcs.length) + '];\n' +
      'static Term *mk_list(int n, Term **xs, Term *tail) { Term *r = tail; for (int i = n; i-- > 0;) r = mk_cons(xs[i], r); return r; }\n' +
      'static void init_tables(void) {\n' + atomInit + '\n' + fnInit + '\n' + kcInit + '\n}\n';
    const natProtos = [...sigs.values()].map(x => x + ';').join('\n') + (refs.size ? REF_C + refFns.join('\n') + '\n' : '');
    // unchecked by default: no step limit, type tests, overflow or zero-divisor tests in native code;
    // opts.checked keeps them (and the step limit) for programs whose calls may break the contract
    const mode = opts.checked ? '#define DL_CHECKED 1 /* checked: step limit, type, overflow and zero tests */\n' : '/* unchecked (the default): calls are assumed to meet the type contract; build with -DDL_CHECKED for the checks */\n';
    const swiMode = opts.swiWrite ? '#define DL_SWI_WRITE 1 /* write/print/format as SWI-Prolog lays terms out */\n' : '';
    const code = header + mode + swiMode + lib + '\n/* ---------- program ---------- */\n' + tables + natLib + protos.join('\n') + '\n' + natProtos + '\n\n' +
      (nDefs.length ? '/* native tier: DET predicates in the modes the queries use */\n' + nDefs.join('\n') + '\n' + natEntries.join('\n') + '\n' : '') +
      defs.join('\n') + '\n' + main;
    return { refs: [...refs.keys()].map(i => qs[i].text), code, warnings, proofs: [...new Set(proofNotes)] };
  }
  P.toC = toC;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog proof checker.  Independent of the converter: it re-derives what it checks.
   1. shape: the Detlog has no cut, ;, ->, \+, findall, call/N or nondeterministic builtin, and every
      predicate has one clause or clauses told apart by distinct first-argument functors;
   2. justification: every Detlog clause carries a proof step with a known rule;
   3. side conditions: S2A tables re-run on the source, MEMO purity and SPLICE independence re-derived,
      FACTS rows compared with the source facts, deterministic builtins re-classified;
   4. evaluation: the answer packets (answers, order, duplicates, output) of the source, both Detlog
      programs and the back-converted Prolog are equal for every query;
   5. run-time determinism: no call had more than one candidate clause. */
(function (P) {
  'use strict';
  const { deref, Cmp, Var, list, listToArray, show, termVars } = P;
  const D = deref;
  const FORBIDDEN = new Set(['!/0', ';/2', '->/2', '*->/2', '\\+/1', 'not/1', 'findall/3', 'findall/4', 'bagof/3', 'setof/3', 'aggregate_all/3', 'aggregate_all/4', 'forall/2', 'once/1', 'ignore/1', 'call/1', 'catch/3']);
  const RULES = new Set(['CUT', 'SPEC', 'PRED', 'FACTS', 'CLAUSE', 'S2A', 'MEMO', 'DET', 'call_det', 'UNSUPPORTED', 'true', 'fail', 'det', 'effect', 'call', 'member_cp', 'between_cp', 'builtin_rows', 'seq', 'det_prefix', 'effect_prefix', 'disj', 'ite', 'ite_det', 'ite_scan', 'neg', 'neg_det', 'neg_scan', 'findall', 'aggregate', 'splice', 'cut_mark']);
  const RUNTIME_PREDS = () => new Set(Object.keys(P.DETLOG_RUNTIME).concat(['if_commit/3']));

  function checkShape(detlogText) {
    const prog = P.loadProgram(detlogText);
    const issues = []; let goals = 0, decisions = 0, condUser = 0;
    const rt = RUNTIME_PREDS();
    for (const k of prog.order) {
      const cls = prog.preds.get(k);
      if (cls.length > 1) {
        const seen = new Set(); let ok = true;
        for (const cl of cls) {
          const h = D(cl.head); const a0 = h.t === 'c' ? D(h.a[0]) : null;
          if (!a0 || a0.t === 'v') { ok = false; break; }
          const key = a0.t === 'c' ? 'c:' + a0.f + '/' + a0.a.length : a0.t + ':' + (a0.n !== undefined ? a0.n : a0.v);
          if (seen.has(key)) { ok = false; break; }
          seen.add(key);
        }
        if (!ok) issues.push(k + ': ' + cls.length + ' clauses not told apart by their first argument (a call would leave a choicepoint)');
      }
      for (const cl of cls) walk(cl.body, k, false);
    }
    function walk(g, k, inCond) {
      g = D(g); const gk = P.key(g);
      if (g.t === 'v') { issues.push(k + ': variable goal (call/N)'); return; }
      if (gk === ',/2') { walk(g.a[0], k, inCond); walk(g.a[1], k, inCond); return; }
      if (gk === 'true/0') return;
      goals++;
      if (gk === 'if_commit/3') { decisions++; walk(g.a[0], k, true); walk(g.a[1], k, inCond); walk(g.a[2], k, inCond); return; }
      if (FORBIDDEN.has(gk) || (gk && gk.startsWith('call/'))) { issues.push(k + ': contains ' + gk); return; }
      if (P.NONDET_BI.has(gk)) { issues.push(k + ': nondeterministic builtin ' + gk + ' called directly'); return; }
      if (prog.preds.has(gk)) { if (inCond) condUser++; return; }
      if (rt.has(gk)) return;
      const b = P.builtins[gk];
      if (b && !b.nondet && !b.call) return;
      issues.push(k + ': unknown goal ' + gk);
    }
    return { ok: issues.length === 0, issues, preds: prog.order.length, clauses: prog.clauses.length, goals, decisions, condUser };
  }

  // purity, re-derived from the source (greatest fixpoint)
  function purity(src) {
    const prog = P.loadProgram(src); const pure = new Map(); const writes = new Map();
    const PURE = new Set(['=/2', 'is/2', '=:=/2', '=\\=/2', '</2', '>/2', '=</2', '>=/2', 'between/3', 'member/2', 'succ/2', 'plus/3', 'true/0']);
    const OUT = new Set(['write/1', 'print/1', 'writeln/1', 'writeq/1', 'write_canonical/1', 'write_term/2', 'nl/0', 'tab/1', 'put_char/1', 'format/1', 'format/2', 'format/3', 'assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'retractall/1', 'nb_setval/2', 'b_setval/2']);
    const calls = new Map();
    for (const k of prog.order) {
      let p = !prog.dynamic.has(k), w = false; const cs = new Set();
      for (const cl of prog.preds.get(k)) (function go(g) {
        g = D(g); const gk = P.key(g);
        if (gk === ',/2' || gk === ';/2') { go(g.a[0]); go(g.a[1]); return; }
        if (prog.preds.has(gk)) { cs.add(gk); return; }
        if (gk && /^(findall|aggregate_all|forall|\\\+|once|ignore|call|maplist|foldl|include|exclude|bagof|setof)\//.test(gk)) { p = false; if (g.t === 'c') g.a.forEach(x => { const xd = D(x); if (xd.t === 'c' || xd.t === 'a') go(xd); }); return; }
        if (gk === '->/2') { p = false; go(g.a[0]); go(g.a[1]); return; }
        if (OUT.has(gk)) { w = true; p = false; return; }
        if (!PURE.has(gk)) p = false;
      })(cl.body);
      pure.set(k, p); writes.set(k, w); calls.set(k, cs);
    }
    let ch = true;
    while (ch) { ch = false; for (const k of prog.order) for (const c of calls.get(k)) { if (pure.get(k) && pure.has(c) && !pure.get(c)) { pure.set(k, false); ch = true; } if (!writes.get(k) && writes.get(c)) { writes.set(k, true); ch = true; } } }
    return { pure, writes, prog };
  }

  function s2aRowsOf(spec) {
    spec = D(spec); const K = D(spec.a[0]).v; const cols = listToArray(spec.a[1]).map(D); const rows = [];
    for (let I = 0; I < K; I++) rows.push(cols.map(c => c.f === 'const' ? c.a[0] : c.f === 'data' ? listToArray(c.a[0])[I] : P.Int(listToArray(c.a[0]).reduce((s, d, i) => s + D(d).v * P.binom(I, i), 0))));
    return rows;
  }

  // full proof: source + conversions (+ back-converted) + run results
  function prove(ctx) {
    const { src, plain, mnn, backPlain, backMnn, runs } = ctx;
    const checks = [];
    const add = (group, name, ok, detail) => checks.push({ group, name, ok, detail: detail || '' });
    const pur = purity(src);
    for (const [label, conv] of [['Detlog', plain], ['MNN Detlog', mnn]]) {
      if (!conv) continue;
      const sh = checkShape(conv.text);
      add('Shape', label + ': no cut, ;, ->, \\+, findall, call/N or nondeterministic builtin; first-argument determinism', sh.ok, sh.ok ? sh.preds + ' predicates, ' + sh.clauses + ' clauses, ' + sh.decisions + ' if_commit decisions' : sh.issues.slice(0, 8).join('; '));
      if (sh.condUser) add('Shape', label + ': if_commit conditions', 'warn', sh.condUser + ' condition(s) call Detlog predicates (allowed: they are deterministic)');
      // justification
      const unjust = conv.clauses.filter(c => !conv.steps[c.step - 1] || !RULES.has(conv.steps[c.step - 1].rule));
      add('Justification', label + ': every clause carries a proof step', unjust.length === 0, conv.clauses.length + ' clauses, ' + conv.steps.length + ' steps (' + summariseRules(conv.steps) + ')');
      // side conditions
      for (const st of conv.steps) {
        if (st.rule === 'S2A') {
          const k = st.pred; const [f, n] = splitKey(k);
          const cl = conv.clauses[st.clauses[0]]; const spec = D(D(cl.term).a[1]).a[0];
          const isPure = pur.pure.get(k);
          const A = []; for (let i = 0; i < +n; i++) A.push(Var());
          const eng = new P.Engine(pur.prog, { stepLimit: 500000 }); const got = [];
          let err = null; try { eng.solve(Cmp(f, A), () => { got.push(A.map(a => P.resolve(a))); return got.length <= 100000; }); } catch (e) { err = e.message; }
          const exp = s2aRowsOf(spec);
          const same = !err && got.length === exp.length && got.every((r, i) => r.every((x, j) => P.compare(x, exp[i][j]) === 0));
          add('Side conditions', 'S2A ' + k + ': pure, and the loop gives exactly the source answers in order', isPure && same, (isPure ? 'pure' : 'NOT pure') + '; ' + got.length + ' source rows vs ' + exp.length + ' loop rows' + (err ? '; ' + err : '') + '; ' + st.info.formula);
        }
        if (st.rule === 'DET') {
          // re-derived from the Detlog itself: nothing reachable from p__d writes output or updates the database,
          // so running it and then the packet code (status maybe) cannot repeat an effect
          const [f, n] = splitKey(st.pred); const dprog = P.loadProgram(conv.text);
          const seen = new Set(); const todo = [f + '__d/' + (+n + 1)]; let bad = null;
          const EFF = new Set(['effect_text/2', 'assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'retractall/1', 'nb_setval/2', 'b_setval/2', 'setarg/3', 'nb_setarg/3']);
          while (todo.length && !bad) {
            const k = todo.pop(); if (seen.has(k)) continue; seen.add(k);
            const cls = dprog.preds.get(k); if (!cls) { bad = 'missing ' + k; break; }
            for (const cl of cls) (function walk(g) { g = D(g); const gk = P.key(g); if (gk === ',/2') { walk(g.a[0]); walk(g.a[1]); return; } if (gk === 'if_commit/3') { g.a.forEach(walk); return; } if (EFF.has(gk) || P.EFFECT.has(gk)) bad = gk; else if (dprog.preds.has(gk)) todo.push(gk); })(cl.body);
          }
          add('Side conditions', 'DET ' + st.pred + ': deterministic mode writes no output (re-derived from the Detlog); status maybe runs the packet code', !bad, bad ? 'reaches ' + bad : seen.size + ' predicate(s) reachable from ' + f + '__d, none writes');
        }
        if (st.rule === 'MEMO') add('Side conditions', 'MEMO ' + st.pred + ': pure (variant calls give equal packets)', !!pur.pure.get(st.pred), pur.pure.get(st.pred) ? 'purity re-derived from the source' : 'not pure');
        if (st.rule === 'splice') {
          let ok = false, why = '';
          try {
            const c = P.readTerm('f(' + st.info.gens[0] + ', ' + st.info.gens[1] + ')').term;
            const va = new Set(termVars(c.a[0]).map(v => v.name)); const shared = termVars(c.a[1]).filter(v => va.has(v.name) && v.name !== '_');
            const outs = [c.a[0], c.a[1]].filter(g => pur.writes.get(P.key(g)));
            ok = !shared.length && !outs.length; why = shared.length ? 'shared: ' + shared.map(v => v.name) : outs.length ? 'a generator writes output' : 'no shared variables, no output; guarded at run time by splice_safe/1';
          } catch (e) { why = e.message; }
          add('Side conditions', 'SPLICE in ' + st.pred + ': ' + st.src, ok, why);
        }
        if (st.rule === 'FACTS' && st.info.n) {
          const k = st.pred; const cl = conv.clauses[st.clauses[0]];
          const rows = st.info.table
            ? listToArray(D(cl.term).a[0]).map(r => P.canonClauses ? show(r, { varName: P.namer() }) : '')
            : listToArray(D(D(cl.term).a[1]).a[0]).map(r => P.canonClauses ? show(D(r).a[0], { varName: P.namer() }) : '');
          const srcRows = pur.prog.preds.get(k).map(c => show(list(D(c.head).t === 'c' ? D(c.head).a : []), { varName: P.namer() }));
          const same = rows.length === srcRows.length && rows.every((r, i) => r === srcRows[i]);
          add('Side conditions', 'FACTS ' + k + ': rows are the source facts in order', same, rows.length + ' facts');
        }
      }
      // first-match scans: the generator is member/2 and every filter is a deterministic builtin
      const scanSteps = conv.steps.filter(s => s.rule === 'ite_scan' || s.rule === 'neg_scan');
      if (scanSteps.length) {
        const badScan = [];
        for (const s of scanSteps) {
          try {
            const gk = P.key(P.readTerm(s.info.gen).term);
            if (s.info.facts) { const cls = pur.prog.preds.get(gk); if (!cls || !cls.length || pur.prog.dynamic.has(gk) || cls.some(c => !(D(c.body).t === 'a' && D(c.body).n === 'true'))) badScan.push(s.info.gen + ' (not a predicate of facts)'); }
            else if (gk !== 'member/2') badScan.push(s.info.gen);
            for (const f of s.info.filters) { const fk = P.key(P.readTerm(f).term); const b = P.builtins[fk]; if (fk !== 'true/0' && (!b || b.nondet || b.call || P.EFFECT.has(fk))) badScan.push(f); }
          } catch (e) { badScan.push(s.src); }
        }
        add('Side conditions', label + ': first-match scans run member/2 or a predicate of facts, with deterministic builtin filters', badScan.length === 0, scanSteps.length + ' scan(s)' + (badScan.length ? '; not allowed: ' + badScan.join(', ') : ''));
      }
      const detSteps = conv.steps.filter(s => s.rule === 'det' || s.rule === 'det_prefix' || s.rule === 'ite_det' || s.rule === 'neg_det');
      let badDet = [];
      for (const s of detSteps) { if (s.rule !== 'det') continue; try { const g = P.readTerm(s.src).term; const gk = P.key(g); const b = P.builtins[gk]; if (!b || b.nondet || b.call || P.EFFECT.has(gk)) badDet.push(gk); } catch (e) { } }
      add('Side conditions', label + ': goals compiled as deterministic are deterministic builtins', badDet.length === 0, detSteps.length + ' deterministic goals' + (badDet.length ? '; not deterministic: ' + badDet.join(', ') : ''));
      if (conv.errors.length) add('Coverage', label + ': predicates converted', false, conv.errors.map(e => e.msg).join('; '));
      else add('Coverage', label + ': every predicate converted', true, conv.genPreds.filter(g => !/^\$query/.test(g.key)).length + ' predicate(s), plus ' + conv.queries.length + ' query predicate(s)');
    }
    // CUT round trip
    for (const [label, back] of [['Detlog', backPlain], ['MNN Detlog', backMnn]]) {
      if (!back) continue;
      const cw = P.changeWarnings(src, back.text, back);
      const same = cw.filter(w => w.kind === 'same').length, changed = cw.filter(w => w.kind === 'changed'), bad = cw.filter(w => w.kind === 'error' || w.kind === 'removed');
      add('Back-conversion', label + ' -> Prolog: predicates restored exactly', bad.length ? false : changed.length ? 'warn' : true, same + ' identical, ' + changed.length + ' changed (equivalent forms), ' + bad.length + ' missing' + (bad.length ? ': ' + bad.map(b => b.pred).join(', ') : ''));
    }
    // evaluation
    if (runs) for (const r of runs) {
      const ref = JSON.stringify(r.prolog.events);
      const parts = [];
      let ok = true; let limitOnly = false;
      for (const [nm, x] of [['Detlog interpreter', r.interp], ['Detlog code', r.plain], ['MNN Detlog code', r.mnn], ['back-converted Prolog', r.back], ['back-converted (MNN) Prolog', r.backMnn]]) {
        if (!x) continue;
        const same = JSON.stringify(x.events) === ref && !x.error === !r.prolog.error;
        if (!same) { ok = false; if (r.prolog.truncated || r.prolog.limit || (x.error && /infinite|no finite packet|step limit/.test(x.error))) limitOnly = true; parts.push(nm + ' differs' + (x.error ? ' (' + x.error + ')' : '')); }
      }
      add('Evaluation', '?- ' + r.query, ok ? true : limitOnly ? 'warn' : false, ok ? r.prolog.answers.length + ' answer(s)' + (r.prolog.output ? ' + output' : '') + ', same order, duplicates and output in Prolog, the Detlog interpreter, both Detlog programs and both back-conversions' : parts.join('; ') + (limitOnly ? ' — infinite generator: no finite packet (documented limit)' : ''));
      for (const [nm, x] of [['Detlog', r.plain], ['MNN', r.mnn]]) if (x && x.violations) add('Determinism', nm + ' ?- ' + r.query, false, x.violations + ' call(s) with more than one candidate clause: ' + x.violationPreds.join(', '));
    }
    if (runs && runs.length) {
      const anyViol = runs.some(r => (r.plain && r.plain.violations) || (r.mnn && r.mnn.violations));
      if (!anyViol) add('Determinism', 'no Detlog call left a choicepoint (first-argument selection was unique on every call)', true, runs.length + ' queries');
    }
    const GO = ['Shape', 'Justification', 'Side conditions', 'Coverage', 'Back-conversion', 'Evaluation', 'Determinism'];
    checks.sort((x, y) => GO.indexOf(x.group) - GO.indexOf(y.group));
    const fails = checks.filter(c => c.ok === false).length, warns = checks.filter(c => c.ok === 'warn').length;
    return { checks, ok: fails === 0, fails, warns, text: proofText(checks, plain, mnn) };
  }
  function summariseRules(steps) { const m = new Map(); for (const s of steps) m.set(s.rule, (m.get(s.rule) || 0) + 1); return [...m].map(([r, n]) => r + ' ' + n).join(', '); }
  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }
  function proofText(checks, plain, mnn) {
    const L = ['pl2detlog proof report', '======================', ''];
    let g = null;
    for (const c of checks) { if (c.group !== g) { L.push('', '## ' + c.group); g = c.group; } L.push((c.ok === true ? '[ok]   ' : c.ok === 'warn' ? '[warn] ' : '[FAIL] ') + c.name + (c.detail ? '\n        ' + c.detail : '')); }
    for (const [label, conv] of [['Detlog (plain)', plain], ['MNN-optimised Detlog', mnn]]) {
      if (!conv) continue;
      L.push('', '## Proof steps: ' + label, '');
      for (const s of conv.steps) {
        if (['true', 'fail', 'det', 'call', 'effect', 'seq', 'member_cp', 'between_cp', 'builtin_rows'].includes(s.rule) && s.clauses.length === 0) { L.push('step ' + s.id + '  ' + s.rule.padEnd(13) + ' ' + s.pred + '  ' + oneLine(s.src)); continue; }
        L.push('step ' + s.id + '  ' + s.rule.padEnd(13) + ' ' + s.pred + '  ' + oneLine(s.src) + (s.clauses.length ? '  -> clauses ' + s.clauses.map(i => i + 1).join(',') : '') + (s.info && s.info.formula ? '  [' + s.info.formula + ']' : ''));
      }
    }
    L.push('', '## Rules', '', ...RULE_DOC.map(([r, d]) => r.padEnd(14) + d));
    return L.join('\n') + '\n';
  }
  function oneLine(s) { s = String(s || '').replace(/\s+/g, ' '); return s.length > 140 ? s.slice(0, 137) + '...' : s; }
  const RULE_DOC = [
    ['CUT', 'H :- G, !, B. Rest  ==>  ( [A..]=[h..], G -> B ; Rest ): cut commits to the first answer of the head match and G'],
    ['SPEC', 'maplist/foldl/include/exclude/partition with a known closure ==> a specialised recursive predicate (no call/N)'],
    ['PRED', 'packet of a predicate = concatenation of its clause packets, in clause order'],
    ['CLAUSE', 'rename the call apart, unify with the head; each env row projected on the head is an answer'],
    ['FACTS', 'packet of facts = the facts that unify with the call, in order'],
    ['seq', 'packet of (A, B) = packet of A with every row replaced by the packet of B in that row'],
    ['disj', 'packet of (A ; B) = packet of A ++ packet of B'],
    ['ite', '(C -> T ; F): output of C up to its first answer, then T on that answer; F if C has none'],
    ['neg', '\\+ G = (G -> fail ; true)'],
    ['ite_scan', '(Pre, member(X, Xs), Post -> T ; F), Pre and Post deterministic builtins: scan Xs in place and stop at the first element that passes'],
    ['neg_scan', '\\+ (Pre, member(X, Xs), Post): the same scan, with T = fail and F = true'],
    ['findall', 'all of G\'s output, then one answer binding the list of template instances (no findall/3)'],
    ['aggregate', 'aggregate_all over the packet of G (count, sum, max, min, bag, set)'],
    ['det', 'a deterministic builtin has at most one answer: if_commit(B, [Env], [])'],
    ['effect', 'output builtins write their text as out(Text) items, in Prolog order'],
    ['member_cp', 'member/between/other nondeterministic builtins: their answers as a packet (builtin_rows)'],
    ['det_prefix', 'MNN: deterministic builtins at the start of a conjunction run in place (no row loop)'],
    ['splice', 'MNN: independent generators computed once and combined by a Cartesian product in Prolog order'],
    ['S2A', 'MNN: a pure predicate with a finite ground table becomes a loop over I = 0..K-1 (Newton formulas, constants or data)'],
    ['cut_mark', 'a cut inside a branch emits [cut, e(Row)]: row loops stop after it and later alternatives and clauses are dropped'],
    ['MEMO', 'MNN: a pure tree-recursive predicate is tabled by call variant'],
    ['call_det', 'MNN: a call of a DET predicate in packet code runs its deterministic mode in place: yes gives [Env], no gives []; maybe undoes it and makes the packet call'],
    ['DET', 'MNN: an output-free predicate whose clauses are told apart by their first argument, and whose goals are deterministic, runs as p__d(Args, Status) without packets; status maybe (a first argument unbound where several clauses match) falls back to the packet code']
  ];
  P.checkShape = checkShape; P.prove = prove; P.purity = purity; P.RULE_DOC = RULE_DOC;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog stats: static complexity of Prolog vs Detlog, per-query steps / time / choicepoints,
   complexity sweeps with a fitted growth class, and the full analysis pipeline used by the app. */
(function (P) {
  'use strict';
  const { deref } = P;
  const D = deref;

  function prologMetrics(src) {
    const prog = typeof src === 'string' ? P.loadProgram(src) : src;
    const m = { predicates: 0, clauses: 0, facts: 0, rules: 0, goals: 0, cuts: 0, disjunctions: 0, ifThenElse: 0, negations: 0, findalls: 0, nondetCalls: 0, choicePreds: 0, recursive: 0, maxBody: 0, choiceSites: 0, cyclomatic: 1 };
    const calls = new Map();
    for (const k of prog.order) {
      const cls = prog.preds.get(k); if (!cls.length) continue;
      m.predicates++; if (cls.length > 1) { m.choicePreds++; m.cyclomatic += cls.length - 1; }
      const cs = new Set();
      for (const cl of cls) {
        m.clauses++;
        const b = D(cl.body);
        if (b.t === 'a' && b.n === 'true') { m.facts++; continue; }
        m.rules++; let len = 0;
        (function walk(g, top) {
          g = D(g); const gk = P.key(g);
          if (gk === ',/2') { walk(g.a[0], top); walk(g.a[1], top); return; }
          if (top) len++;
          m.goals++;
          if (gk === '!/0') { m.cuts++; return; }
          if (gk === ';/2') { const l = D(g.a[0]); if (l.t === 'c' && l.f === '->') { m.ifThenElse++; m.cyclomatic++; walk(l.a[0], false); walk(l.a[1], false); } else { m.disjunctions++; m.cyclomatic++; walk(g.a[0], false); } walk(g.a[1], false); return; }
          if (gk === '->/2') { m.ifThenElse++; m.cyclomatic++; walk(g.a[0], false); walk(g.a[1], false); return; }
          if (gk === '\\+/1' || gk === 'not/1') { m.negations++; m.cyclomatic++; walk(g.a[0], false); return; }
          if (/^(findall|bagof|setof|aggregate_all|forall)\//.test(gk)) { m.findalls++; walk(g.a[1], false); return; }
          if (P.NONDET_BI.has(gk)) { m.nondetCalls++; m.cyclomatic++; }
          if (prog.preds.has(gk)) cs.add(gk);
        })(cl.body, true);
        m.maxBody = Math.max(m.maxBody, len);
      }
      calls.set(k, cs);
    }
    // recursion via reachability
    for (const k of calls.keys()) { const seen = new Set(); const st = [...calls.get(k)]; let rec = false; while (st.length) { const x = st.pop(); if (x === k) { rec = true; break; } if (seen.has(x)) continue; seen.add(x); for (const y of calls.get(x) || []) st.push(y); } if (rec) m.recursive++; }
    m.choiceSites = m.choicePreds + m.disjunctions + m.nondetCalls;
    return m;
  }
  function detlogMetrics(text) {
    const prog = P.loadProgram(text);
    const m = { predicates: 0, clauses: 0, goals: 0, decisions: 0, auxPredicates: 0, runtimeCalls: 0, packetPreds: 0, choiceSites: 0, maxBody: 0, cyclomatic: 1 };
    const rt = new Set(Object.keys(P.DETLOG_RUNTIME));
    for (const k of prog.order) {
      const cls = prog.preds.get(k); m.predicates++;
      if (/__cp\/\d+$/.test(k)) m.packetPreds++; else m.auxPredicates++;
      if (cls.length > 1) m.cyclomatic += cls.length - 1;
      for (const cl of cls) {
        m.clauses++; let len = 0;
        (function walk(g) { g = D(g); const gk = P.key(g); if (gk === ',/2') { walk(g.a[0]); walk(g.a[1]); return; } len++; m.goals++; if (gk === 'if_commit/3') { m.decisions++; m.cyclomatic++; walk(g.a[0]); walk(g.a[1]); walk(g.a[2]); return; } if (rt.has(gk)) m.runtimeCalls++; })(cl.body);
        m.maxBody = Math.max(m.maxBody, len);
      }
    }
    m.choiceSites = 0;
    return m;
  }

  // run fn repeatedly to time it: returns mean ms per run
  // time fn: warm up (so every engine is measured after JIT compilation), then the median of 5 batches
  function timeIt(fn, budgetMs, maxReps, setup) {
    budgetMs = budgetMs || 30; maxReps = maxReps || 2000;
    const one = () => { const s = setup ? setup() : undefined; const t = P.now(); const r = fn(s); return { dt: P.now() - t, r }; };
    let last = one(); if (last.r && last.r.error) return { ms: last.dt, reps: 1, last: last.r };
    const wall = P.now(); let w = 0; while (P.now() - wall < budgetMs / 6 && w < 50) { one(); w++; } // warm-up
    const est = Math.max(1e-4, (P.now() - wall) / Math.max(1, w));
    const per = Math.max(1, Math.min(maxReps, Math.floor((budgetMs / 6) / est)));
    const batches = [];
    for (let b = 0; b < 5; b++) { let tot = 0; for (let i = 0; i < per; i++) { const x = one(); tot += x.dt; last = x; } batches.push(tot / per); }
    batches.sort((a, b) => a - b);
    return { ms: batches[2], reps: per * 5, last: last.r };
  }

  // growth class from (n, steps) points
  function fitGrowth(pts) {
    pts = pts.filter(p => p.x > 0 && p.y > 0);
    if (pts.length < 3) return { label: 'n/a', k: null };
    const lr = (xs, ys) => { const n = xs.length; const mx = xs.reduce((a, b) => a + b) / n, my = ys.reduce((a, b) => a + b) / n; let sxy = 0, sxx = 0, syy = 0; for (let i = 0; i < n; i++) { sxy += (xs[i] - mx) * (ys[i] - my); sxx += (xs[i] - mx) ** 2; syy += (ys[i] - my) ** 2; } const b = sxx ? sxy / sxx : 0; const r2 = sxx && syy ? (sxy * sxy) / (sxx * syy) : 1; return { b, r2 }; };
    const lx = pts.map(p => Math.log(p.x)), ly = pts.map(p => Math.log(p.y)), x = pts.map(p => p.x);
    const pw = lr(lx, ly), ex = lr(x, ly);
    const spread = Math.max(...pts.map(p => p.y)) / Math.min(...pts.map(p => p.y));
    if (spread < 1.15) return { label: 'O(1)', k: 0, r2: 1 };
    if (ex.r2 > pw.r2 + 0.01 && ex.b > 0.08 && pw.b > 1.5) return { label: 'O(' + Math.exp(ex.b).toFixed(2) + '^n)', k: pw.b, r2: ex.r2, exp: true, base: Math.exp(ex.b) };
    const k = pw.b; let label;
    if (k < 0.2) label = 'O(1)'; else if (k < 0.75) label = 'O(log n) – O(√n)'; else if (k < 1.15) label = 'O(n)'; else if (k < 1.5) label = 'O(n log n)'; else if (k < 2.5) label = 'O(n²)'; else if (k < 3.5) label = 'O(n³)'; else label = 'O(n^' + k.toFixed(1) + ')';
    return { label, k, r2: pw.r2 };
  }
  function parseRange(s) {
    s = String(s || '').trim(); if (!s) return [];
    const m = /^(-?\d+)\s*\.\.\s*(-?\d+)(?:\s*(?:by|step|:)\s*(\d+))?$/.exec(s);
    if (m) { const a = +m[1], b = +m[2], st = +(m[3] || 1); const out = []; for (let i = a; i <= b && out.length < 60; i += st) out.push(i); return out; }
    return s.split(/[\s,]+/).map(Number).filter(n => Number.isFinite(n)).slice(0, 60);
  }

  // ---------- the analysis pipeline ----------
  // opts: { mnn: {fuse, splice, s2a, memo}, sweep: {template, values}, timing: bool, stepLimit }
  function analyse(src, queries, opts) {
    opts = opts || {};
    const res = { errors: [], warnings: [] };
    queries = queries.map(q => q.trim().replace(/\.\s*$/, '')).filter(Boolean);
    const sweepVals = opts.sweep && opts.sweep.template ? parseRange(opts.sweep.values) : [];
    const sweepQs = sweepVals.map(v => opts.sweep.template.replace(/\bN\b|\{N\}|\$N/g, String(v)));
    const allQs = queries.concat(sweepQs);
    const t0 = P.now();
    try { P.loadProgram(src); } catch (e) { res.errors.push(e.message); return res; }
    res.plain = P.convert(src, { mnn: false, queries: allQs });
    res.convertMs = P.now() - t0;
    const t1 = P.now();
    res.mnn = P.convert(src, Object.assign({ mnn: true, queries: allQs }, opts.mnn || {}));
    res.convertMnnMs = P.now() - t1;
    const progPlain = P.loadProgram(res.plain.text), progMnn = P.loadProgram(res.mnn.text);
    try { progMnn.pairwiseSource = P.loadProgram(res.mnn.source); } catch (e) { /* the JIT then permutes in full */ }
    try { res.backPlain = P.backConvert(res.plain.text); } catch (e) { res.backPlain = null; res.errors.push('back-conversion (plain): ' + e.message); }
    try { res.backMnn = P.backConvert(res.mnn.text); } catch (e) { res.backMnn = null; res.errors.push('back-conversion (MNN): ' + e.message); }
    res.changes = res.backPlain ? P.changeWarnings(src, res.backPlain.text, res.backPlain) : [];
    res.changesMnn = res.backMnn ? P.changeWarnings(src, res.backMnn.text, res.backMnn) : [];
    const backProg = res.backPlain ? safeLoad(res.backPlain.text) : null, backMnnProg = res.backMnn ? safeLoad(res.backMnn.text) : null;
    const lim = opts.stepLimit || 3e6;
    const sharedProg = P.loadProgram(src);
    const dynamic = sharedProg.dynamic.size > 0 || /\b(assert[az]?|retract(all)?)\s*\(/.test(src);
    const runOne = (qi) => {
      const q = res.plain.queries[qi], qm = res.mnn.queries[qi];
      if (q.error) return { query: q.text, error: q.error, prolog: { events: [], answers: [], error: q.error } };
      const r = { query: q.text };
      const fresh = () => P.loadProgram(src); // assert/retract must not leak between runs
      r.prolog = P.runQuery(fresh(), q.text, { stepLimit: lim, maxAnswers: 1000 });
      r.interp = P.runDetlogInterp(res.plain, q.pred, q.vars, { stepLimit: lim * 20 });
      r.plain = P.runDetlogFast(progPlain, q.pred, q.vars, { stepLimit: lim * 20 });
      r.mnn = P.runDetlogFast(progMnn, qm.pred, qm.vars, { stepLimit: lim * 20 });
      if (backProg) r.back = P.runQuery(safeLoad(res.backPlain.text), q.text, { stepLimit: lim, maxAnswers: 1000 });
      if (backMnnProg) r.backMnn = P.runQuery(safeLoad(res.backMnn.text), q.text, { stepLimit: lim, maxAnswers: 1000 });
      const ev = JSON.stringify(r.prolog.events);
      r.same = ev === JSON.stringify(r.plain.events) && ev === JSON.stringify(r.mnn.events) && ev === JSON.stringify(r.interp.events);
      if (opts.timing !== false) {
        const parsedQ = P.readTerm(q.text);
        r.prolog.ms = timeIt(pr => P.runQuery(pr, parsedQ, { stepLimit: lim, maxAnswers: 1000 }), 25, 200, dynamic ? fresh : () => sharedProg).ms;
        r.interp.ms = timeIt(() => P.runDetlogInterp(res.plain, q.pred, q.vars, { stepLimit: lim * 20 })).ms;
        r.plain.ms = timeIt(() => P.runDetlogFast(progPlain, q.pred, q.vars, { stepLimit: lim * 20 })).ms;
        r.mnn.ms = timeIt(() => P.runDetlogFast(progMnn, qm.pred, qm.vars, { stepLimit: lim * 20 })).ms;
        // against the same algorithm written by hand: MNN Detlog's computation alone, as the reference measures
        if (P.cReference && !r.mnn.error) {
          r.cref = P.cReference(q.text, r.mnn.events);
          if (r.cref) r.mnn.computeMs = timeIt(() => P.runDetlogFast(progMnn, qm.pred, qm.vars, { stepLimit: lim * 20, noDecode: true })).ms;
        }
      }
      return r;
    };
    res.runs = queries.map((_, i) => runOne(i));
    if (sweepVals.length) {
      const pts = sweepVals.map((v, j) => { const r = runOne(queries.length + j); return { n: v, query: sweepQs[j], prolog: r.prolog, interp: r.interp, plain: r.plain, mnn: r.mnn, same: r.same }; });
      const fit = key => fitGrowth(pts.filter(p => !p[key].error).map(p => ({ x: p.n, y: p[key].steps })));
      res.sweep = { template: opts.sweep.template, points: pts, fit: { prolog: fit('prolog'), interp: fit('interp'), plain: fit('plain'), mnn: fit('mnn') } };
    }
    res.metrics = { prolog: prologMetrics(src), plain: detlogMetrics(res.plain.text), mnn: detlogMetrics(res.mnn.text) };
    res.proof = P.prove({ src, plain: res.plain, mnn: res.mnn, backPlain: res.backPlain, backMnn: res.backMnn, runs: res.runs });
    // hide sweep queries from the converted text shown to the user? keep them: they are converted like any query
    res.totalMs = P.now() - t0;
    return res;
  }
  function safeLoad(t) { try { return P.loadProgram(t); } catch (e) { return null; } }

  P.prologMetrics = prologMetrics; P.detlogMetrics = detlogMetrics; P.fitGrowth = fitGrowth; P.parseRange = parseRange; P.analyse = analyse; P.timeIt = timeIt;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* pl2detlog C reference: how a query's time compares with the same algorithm written by hand in C.
   The app can't compile C, so it times the hand-written JavaScript version of the algorithm (as in
   bench/reference.js) on this machine and scales it by C's time over JavaScript's for that algorithm, as
   measured by bench/compare.js (cc -O2 and Node).  A reference applies to a query only when its answers are
   exactly the program's answers, so a program that defines fib/2 differently gets no C comparison. */
(function (P) {
  'use strict';
  const cons = (h, t) => ({ h, t });
  const toArr = l => { const a = []; for (; l !== null; l = l.t) a.push(l.h); return a; };
  const show = a => '[' + a.join(', ') + ']';
  function fib(n) { if (n === 0) return 0; if (n === 1) return 1; return fib(n - 1) + fib(n - 2); }
  function app(a, l) { return a === null ? l : cons(a.h, app(a.t, l)); }
  function nrev(l) { return l === null ? null : app(nrev(l.t), cons(l.h, null)); }
  function numlist(lo, hi) { let r = null; for (let i = hi; i >= lo; i--) r = cons(i, r); return r; }
  function doubles(l) { return l === null ? null : cons(2 * l.h, doubles(l.t)); }
  function total(l) { let s = 0; for (; l !== null; l = l.t) s += l.h; return s; }
  function safe(qs) { for (let i = 0; i < qs.length; i++) for (let j = i + 1, d = 1; j < qs.length; j++, d++) if (qs[i] === qs[j] + d || qs[i] === qs[j] - d) return false; return true; }
  function queens(n) {
    const sols = [], out = new Array(n), used = new Array(n).fill(false);
    (function perm(k) {
      if (k === n) { if (safe(out)) sols.push(out.slice()); return; }
      for (let i = 0; i < n; i++) if (!used[i]) { used[i] = true; out[k] = i + 1; perm(k + 1); used[i] = false; }
    })(0);
    return sols;
  }
  function pin() { const r = []; for (let a = 0; a <= 9; a++) for (let b = 0; b <= 9; b++) for (let c = 0; c <= 9; c++) if (a + b + c === 25) r.push([a, b, c]); return r; }
  const par = [[0, 1], [1, 2], [2, 3]], PEOPLE = ['ann', 'bob', 'cy', 'dee'];
  function ancBB(z, y) { let n = 0; for (const [a, b] of par) if (a === z && b === y) n++; for (const [a, b] of par) if (a === z) n += ancBB(b, y); return n; }
  function anc(y) { const r = []; for (const [a, b] of par) if (b === y) r.push(a); for (const [a, b] of par) for (let k = ancBB(b, y); k > 0; k--) r.push(a); return r; }

  // C time / JavaScript time per algorithm (bench/results.json: hand-written C with cc -O2, hand-written JS on Node)
  const C_OVER_JS = { fib: 0.143, nrev: 0.50, doubles: 0.41, queens: 0.21, pin: 0.39, anc: 0.0105 };
  const N = s => { const n = +s; return Number.isInteger(n) && n >= 0 ? n : null; };
  // each: query pattern -> { alg, run: () => result, rows: result -> expected answer texts }; sizes are capped
  // so that the reference never takes long (the query itself has already run)
  const REFS = [
    [/^fib\((\d+),\s*F\)$/, m => { const n = N(m[1]); return n !== null && n <= 32 && { alg: 'fib', n, run: () => fib(n), rows: v => ['F = ' + v] }; }],
    [/^numlist\(1,\s*(\d+),\s*L\),\s*nrev\(L,\s*R\)$/, m => { const n = N(m[1]); return n !== null && n >= 1 && n <= 3000 && { alg: 'nrev', n, run: () => nrev(numlist(1, n)), rows: r => { const a = toArr(r); return ['L = ' + show(a.slice().reverse()) + ', R = ' + show(a)]; } }; }],
    [/^numlist\(1,\s*(\d+),\s*L\),\s*doubles\(L,\s*D\),\s*total\(D,\s*S\)$/, m => { const n = N(m[1]); return n !== null && n >= 1 && n <= 100000 && { alg: 'doubles', n, run: () => total(doubles(numlist(1, n))), rows: s => { const a = toArr(numlist(1, n)); return ['L = ' + show(a) + ', D = ' + show(a.map(x => 2 * x)) + ', S = ' + s]; } }; }],
    [/^queens\((\d+),\s*Qs\)$/, m => { const n = N(m[1]); return n !== null && n >= 1 && n <= 9 && { alg: 'queens', n, run: () => queens(n), rows: s => s.map(q => 'Qs = ' + show(q)) }; }],
    [/^pin\(A,\s*B,\s*C\)$/, () => ({ alg: 'pin', n: 0, run: pin, rows: s => s.map(([a, b, c]) => 'A = ' + a + ', B = ' + b + ', C = ' + c) })],
    [/^anc\(X,\s*dee\)$/, () => ({ alg: 'anc', n: 3, run: () => anc(3), rows: s => s.map(i => 'X = ' + PEOPLE[i]) })],
  ];
  // ms per run, timed in batches (the clock is read per batch, not per run, as nanosecond runs need):
  // after a warm-up, the batch size is set so a batch takes about 4 ms; the median of 3 batches
  let sink = 0;
  function batchTime(fn) {
    const w = P.now(); while (P.now() - w < 60) sink ^= (fn() ? 1 : 0); // warm-up, so the code is optimised
    let n = 1;
    for (;;) { const t = P.now(); for (let i = 0; i < n; i++) sink ^= (fn() ? 1 : 0); const dt = P.now() - t; if (dt > 4 || n >= 1 << 24) break; n = dt < 0.5 ? n * 8 : Math.ceil(n * 4.5 / dt); }
    const ts = [];
    for (let b = 0; b < 3; b++) { const t = P.now(); for (let i = 0; i < n; i++) sink ^= (fn() ? 1 : 0); ts.push((P.now() - t) / n); }
    return ts.sort((a, b) => a - b)[1];
  }
  // q: the query text; events: the program's answer events.  Returns null, or
  // { alg, jsMs (hand-written JavaScript, timed here), cMs (estimated C on this machine), ratio }
  // the benchmark algorithm a query runs, or null: its pattern matches (cRefPattern) and the hand-written
  // version's answers are exactly the program's answers (cRefMatch)
  function cRefPattern(q) {
    q = q.trim().replace(/\.\s*$/, '');
    for (const [re, mk] of REFS) { const m = q.match(re); if (m) return mk(m) || null; }
    return null;
  }
  function cRefMatch(q, events) {
    const ref = cRefPattern(q); if (!ref) return null;
    const exp = ref.rows(ref.run());
    if (!events || events.some(e => e.k !== 'row') || events.length !== exp.length || events.some((e, i) => e.text !== exp[i])) return null;
    return ref;
  }
  function cReference(q, events) {
    const ref = cRefMatch(q, events); if (!ref) return null;
    const jsMs = batchTime(ref.run);
    return { alg: ref.alg, jsMs, cMs: jsMs * C_OVER_JS[ref.alg], ratio: C_OVER_JS[ref.alg] };
  }
  // the C export of the MNN Detlog against the hand-written C, both compiled with cc -O2 on one machine
  // (bench/results.json; µs per run)
  const C_EXPORT_RECORDED = {
    "fib(18, F)": { c: 2.9501, mnnC: 2.6 },
    "fib(21, F)": { c: 15.713, mnnC: 4 },
    "numlist(1, 60, L), nrev(L, R)": { c: 5.1872, mnnC: 17.1 },
    "numlist(1, 300, L), nrev(L, R)": { c: 161.4897, mnnC: 475.7 },
    "numlist(1, 2000, L), doubles(L, D), total(D, S)": { c: 10.9991, mnnC: 106 },
    "queens(6, Qs)": { c: 8.2256, mnnC: 132.8 },
    "queens(7, Qs)": { c: 62.2202, mnnC: 1005.5 },
    "pin(A, B, C)": { c: 0.5094, mnnC: 4.1 },
    "anc(X, dee)": { c: 0.0025, mnnC: 3.6 }
  };
  P.cReference = cReference; P.cRefPattern = cRefPattern; P.cRefMatch = cRefMatch; P.C_OVER_JS = C_OVER_JS; P.C_EXPORT_RECORDED = C_EXPORT_RECORDED;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

(function(P){P.EXAMPLES=[
 {
  "id": "fib",
  "title": "Fibonacci: exponential Prolog, linear MNN Detlog",
  "src": "% Tree recursion: Prolog recomputes fib(N-2) inside fib(N-1).\n% MNN Detlog tables the pure predicate by call variant (rule MEMO)\n% and splices the two independent recursive calls (rule splice).\nfib(0, 0).\nfib(1, 1).\nfib(N, F) :-\n    N > 1,\n    N1 is N - 1,\n    N2 is N - 2,\n    fib(N1, F1),\n    fib(N2, F2),\n    F is F1 + F2.\n",
  "queries": [
   "fib(15, F)",
   "fib(10, F)"
  ],
  "sweep": "fib(N, F)",
  "values": "2..18 by 2"
 },
 {
  "id": "cuts",
  "title": "Cuts of several kinds",
  "src": "% Cuts of several kinds.  detlog2 turns each into an explicit decision.\n\n% a :- b, !, c.  a :- d.   becomes   a :- if_commit(b, c, d).\na(X) :- b(X), !, c(X).\na(X) :- d(X).\nb(1). b(2).\nc(1).\nd(3).\n\n% A red cut (meaning-changing) and a green one.\nmax(X, Y, X) :- X >= Y, !.\nmax(_, Y, Y).\n\nclassify(N, neg) :- N < 0, !.\nclassify(0, zero) :- !.\nclassify(_, pos).\n\n% First solution only, with a cut local to findall's goal.\nfirsts(L, F) :- findall(X, (member(X, L), X > 1, !), F).\n\n% Two cuts in one clause.\ntwo(X, Y) :- member(X, [1, 2, 3]), X > 1, !, member(Y, [a, b]), !.\ntwo(none, none).\n\n% A cut inside \\+ is local to it.\nno_big(L) :- \\+ (member(X, L), X > 5, !).\n\n% \"!\" here is data (a character list), not a cut.\nbang(Out) :- append(\"Hi\", \"!\", Out).\n",
  "queries": [
   "a(X)",
   "a(3)",
   "max(5, 3, Z)",
   "max(1, 3, Z)",
   "classify(0, C)",
   "classify(-4, C)",
   "firsts([1,2,3], F)",
   "two(X, Y)",
   "no_big([1,2])",
   "no_big([7])"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "branchcut",
  "title": "A cut inside an if-then-else branch",
  "src": "% The cut in the then-branch cuts the whole clause: member/2's later\n% answers and pick/2's second clause.  Detlog writes it as a cut marker:\n% the row loop stops after it and the later clause is dropped.\npick(N, X) :- ( N > 3 -> member(X, [big, huge]), ! ; X = small ).\npick(_, other).\n\nfirst_over(L, Min, X) :- member(X, L), ( X > Min -> ! ; fail ).\nfirst_over(_, _, none).\n\nw(X) :- member(X, [1, 2, 3]), write(X), ( X >= 2 -> nl, ! ; true ).\nw(last).\n",
  "queries": [
   "pick(5, X)",
   "pick(2, X)",
   "first_over([1,5,9], 3, X)",
   "first_over([1,2], 3, X)",
   "w(X)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "splice",
  "title": "Splicing independent generators",
  "src": "% The splice example from the Detlog notes: two generators whose answers\n% are combined.  detlog2 computes each packet once and splices them:\n%   ?- c(A, B).   A = 1, B = 3 ; A = 1, B = 4 ; A = 2, B = 3 ; A = 2, B = 4.\n\nc(A, B) :- a(A), b(B).\na(A) :- member(A, [1, 2]).\nb(B) :- member(B, [3, 4]).\n\n% Three positions, one of them fixed: splice([fixed, cp([1,2]), x], Rows).\ntriple(X, Y, Z) :- X = fixed, member(Y, [1, 2]), Z = x.\n\n% A dependent conjunction: q/2 needs the answer of p/1.\np(1). p(2). p(3).\nq(X, Y) :- p(X), Y is X * 10, Y > 10.\n\n% a larger product: three independent generators\ndigit(D) :- between(0, 9, D).\npin(A, B, C) :- digit(A), digit(B), digit(C), A + B + C =:= 25.\n",
  "queries": [
   "c(A, B)",
   "triple(X, Y, Z)",
   "q(X, Y)",
   "pin(A, B, C)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "unfold",
  "title": "Data unfolded into S2A loops",
  "src": "/*  unfold.pl - data and the rules over it, for detlog2 unfold.\n\n    detlog2 unfold examples/unfold.pl -o out.pl --check 'step(X, 13)'\n\n    Every pure predicate is unfolded into its answer table, and each table\n    becomes an S2A loop.  first_colour/1 has a cut and evens/1 has infinitely\n    many answers, so they are converted as usual instead.\n*/\n\n% facts with a pattern: V = 3 + 5*I\nstep(0, 3).\nstep(1, 8).\nstep(2, 13).\nstep(3, 18).\nstep(4, 23).\n\n% data computed by rules\nsquare(N, S) :- between(0, 6, N), S is N * N.\ntriangle(N, T) :- between(0, 9, N), T is N * (N + 1) // 2.\ncube(N, C) :- between(0, 5, N), C is N * N * N - 2.\n\n% facts with no formula: the values are listed\ncolour(0, red).\ncolour(1, green).\ncolour(2, blue).\n\n% rules over the data, recursion included\npair(N, S, C) :- square(N, S), N < 3, colour(N, C).\ntwo_steps(X, Z) :- step(X, Y), step(Y, Z).\nparent(ann, bob).\nparent(bob, cy).\nparent(cy, dee).\nanc(X, Y) :- parent(X, Y).\nanc(X, Y) :- parent(X, Z), anc(Z, Y).\neither(X) :- ( X = 1 ; X = 2 ; X = 1 ).\n\n% not pure: converted, not unfolded (it calls colour/2's loop)\nfirst_colour(C) :- colour(_, C), !.\n\n% infinitely many answers: converted, not unfolded\nevens(X) :- between(0, inf, Y), X is 2 * Y.\n",
  "queries": [
   "step(X, 13)",
   "square(N, 25)",
   "triangle(N, T)",
   "cube(3, C)",
   "pair(N, S, C)",
   "two_steps(X, Z)",
   "anc(X, dee)",
   "either(X)",
   "first_colour(C)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "output",
  "title": "Output written from inside generators",
  "src": "% Output written from inside generators.  In converted code output is data\n% (out(Text) items of the answer packets), so it comes out in exactly the\n% order Prolog writes it.\n\ngen(X) :- member(X, [1, 2]), write(g(X)).\n\n% g(1)s(1)  then  g(2)s(2): the generator's output interleaves with the caller's\nshow :- gen(X), write(s(X)), nl, fail.\nshow.\n\n% two writing generators in one conjunction\npairs :- gen(X), gen(Y), write(X-Y), nl, fail.\npairs.\n\n% commitment stops output at the first answer\nfirst_big(X) :- once((member(X, [1, 5, 9]), write(try(X)), X > 3)).\n\n% output inside findall/3 and aggregate_all/3\ncount_out(N) :- aggregate_all(count, gen(_), N).\nlogged(L) :- findall(X, (gen(X), write(','), X > 0), L), nl.\n",
  "queries": [
   "show",
   "pairs",
   "first_big(X)",
   "count_out(N)",
   "logged(L)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "lists",
  "title": "Lists, higher-order, aggregates, DCG",
  "src": "% a broader program\nnrev([], []).\nnrev([H|T], R) :- nrev(T, RT), app(RT, [H], R).\napp([], L, L).\napp([H|T], L, [H|R]) :- app(T, L, R).\nlen([], 0).\nlen([_|T], N) :- len(T, M), N is M + 1.\ndouble(X, Y) :- Y is 2 * X.\nadd(X, A0, A) :- A is A0 + X.\ndoubles(L, D) :- maplist(double, L, D).\ntotal(L, S) :- foldl(add, L, 0, S).\nscale(K, L, R) :- maplist([X, Y]>>(Y is K * X), L, R).\nsum_with(L, S) :- foldl([X, A0, A]>>(A is A0 + X), L, 0, S).\nsmall(L, S) :- exclude([X]>>(X > 2), L, S).\nsplit(L, I, E) :- partition(even, L, I, E).\nevens(L, E) :- include(even, L, E).\neven(X) :- 0 is X mod 2.\ncolour(red). colour(green). colour(blue).\nsize(small). size(large).\ncombo(C-S) :- colour(C), size(S).\ncount_combos(N) :- aggregate_all(count, combo(_), N).\nmax_len(M) :- aggregate_all(max(L), (colour(C), atom_length(C, L)), M).\nsorted(Cs) :- setof(C, colour(C), Cs).\ngreet(Name) :- format(\"hello ~w~n\", [Name]).\ngreet_all :- forall(colour(C), greet(C)).\nclassify(X, small) :- X < 10.\nclassify(X, big) :- X >= 10, X < 100.\nclassify(_, huge).\nfirst_class(X, C) :- once(classify(X, C)).\nnot_red(C) :- colour(C), \\+ C = red.\npath(a, b). path(b, c). path(c, d).\nreach(X, Y) :- path(X, Y).\nreach(X, Y) :- path(X, Z), reach(Z, Y).\ndigits([D|T]) --> digit(D), digits(T).\ndigits([D]) --> digit(D).\ndigit(D) --> [D], { code_type(D, digit) }.\nparse(S, N) :- atom_codes(S, Cs), phrase(digits(Ds), Cs), number_codes(N, Ds).\nalt(X) :- ( X = 1 ; X = 2 ; X = 3 ).\nnested(X, R) :- ( X > 0 -> ( X > 5 -> R = big ; R = small ) ; R = neg ).\nwords(S, W) :- split_string(S, \" \", \"\", Parts), length(Parts, W).\nhanoi(0, _, _, _) :- !.\nhanoi(N, A, B, C) :- N1 is N - 1, hanoi(N1, A, C, B), hanoi(N1, C, B, A).\nqueens(N, Qs) :- numlist(1, N, Ns), permutation(Ns, Qs), safe(Qs).\nsafe([]).\nsafe([Q|Qs]) :- no_attack(Q, Qs, 1), safe(Qs).\nno_attack(_, [], _).\nno_attack(Q, [Q1|Qs], D) :- Q =\\= Q1 + D, Q =\\= Q1 - D, D1 is D + 1, no_attack(Q, Qs, D1).\n",
  "queries": [
   "nrev([1,2,3,4], R)",
   "app(X, Y, [a,b])",
   "doubles([1,2,3], D)",
   "total([1,2,3,4], S)",
   "scale(3, [1,2], R)",
   "evens([1,2,3,4,5,6], E)",
   "split([1,2,3,4], I, E)",
   "count_combos(N)",
   "sorted(Cs)",
   "greet_all",
   "not_red(C)",
   "reach(a, Y)",
   "parse('123', N)",
   "nested(7, R)",
   "words(\"a b c\", W)",
   "queens(5, Qs)"
  ],
  "sweep": "numlist(1, N, L), nrev(L, R)",
  "values": "4..40 by 4"
 },
 {
  "id": "queens",
  "title": "N-queens by generate and test",
  "src": "queens(N, Qs) :- numlist(1, N, Ns), permutation(Ns, Qs), safe(Qs).\nsafe([]).\nsafe([Q|Qs]) :- no_attack(Q, Qs, 1), safe(Qs).\nno_attack(_, [], _).\nno_attack(Q, [Q1|Qs], D) :-\n    Q =\\= Q1 + D, Q =\\= Q1 - D,\n    D1 is D + 1,\n    no_attack(Q, Qs, D1).\n",
  "queries": [
   "queens(4, Qs)",
   "queens(6, Qs)"
  ],
  "sweep": "queens(N, Qs)",
  "values": "3..7"
 },
 {
  "id": "scan",
  "title": "First-match scans: committed member/2 conditions",
  "src": "% First-match scans (rules ite_scan and neg_scan).\n% A committed condition (member(X, Xs), Filters) becomes one recursive scan\n% that stops at the first element passing the filters, as Prolog does:\n% later elements are never tested, so they cannot raise errors.\n\n% A cut local to findall's goal.\nfirsts(L, F) :- findall(X, (member(X, L), X > 1, !), F).\n\n% once/1, and an if-then-else with a real then-branch.\nfirst_big(L, X) :- once((member(X, L), X > 10)).\nlabel(L, R) :- ( member(X, L), X mod 2 =:= 0 -> R = even(X) ; R = none ).\n\n% \\+ is the same scan with T = fail and F = true.\nall_small(L) :- \\+ (member(X, L), X >= 10).\n\n% The element can be a pattern; a deterministic prefix runs once.\nkey_of(K, Pairs, V) :- once(member(K-V, Pairs)).\nabove(N, L, Y) :- ( M is N * 2, member(Y, L), Y > M -> true ; Y = none ).\n",
  "queries": [
   "firsts([0,3,5], F)",
   "firsts([2,a], F)",
   "first_big([3,20,x], X)",
   "label([1,4,6], R)",
   "label([1,3], R)",
   "all_small([1,2])",
   "all_small([1,12,a])",
   "key_of(b, [a-1,b-2,b-3], V)",
   "above(2, [1,5,9], Y)",
   "above(5, [1,5], Y)"
  ],
  "sweep": "",
  "values": ""
 }
];})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* thermo.js - the thermodynamic compression MNN of mnns (prolog/thermo/thermo.pl), in JavaScript,
   and a lossless store for data the interpreter keeps (src/interp.js).

   A sequence is coded as { alphabet, counts, rank }: its sorted distinct symbols, how often each
   occurs, and its rank, from 0, among all sequences with exactly those counts in dictionary order
   (enumerative coding). For length N and counts c1..ck there are M = N! / (c1! ... ck!) such
   sequences and their ranks are exactly 0..M-1, so the rank needs ceil(log2 M) bits; no code that
   tells them apart can use fewer (pigeonhole), and log2 M =< N * H(counts).

   The rank is a sum of one neuron per position: with M and N for the counts still left, a position
   holding the I-th symbol fires with weight M * (c1 + ... + c(I-1)) / N. Each M * cj / N is the
   multinomial with cj lowered by one (Pascal's rule), a whole number, and the k blocks of sizes
   M * cj / N tile 0..M-1. Decoding finds the block that holds the rank: with q = floor(R * N / M),
   R lies in block j exactly when P_j =< q < P_(j+1) (P the prefix sums of the counts), because
   R * N < M * P <=> q < P for whole P. So each position costs a few multiplies and divides.

   The coder is a bijection on the class, so it erases nothing (Landauer: no heat needed).

   pack(text) stores a string in blocks of symbols (UTF-16 code units), each block as a bitmap of
   the symbols it uses, their counts (Elias gamma) and its rank in exactly ceil(log2 M) bits. */
(function (P) {
  'use strict';
  const big = BigInt;
  const sortSyms = (xs) => [...new Set(xs)].sort((a, b) => (typeof a === 'number' && typeof b === 'number' ? a - b : String(a) < String(b) ? -1 : String(a) > String(b) ? 1 : 0));

  function multinomial(counts) {
    // N! / prod ci!, built as a product of binomials so that every step is whole
    let m = 1n, n = 0;
    for (const c of counts) for (let i = 1; i <= c; i++) { n++; m = m * big(n) / big(i); }
    return m;
  }
  const bitsFor = (v) => (v <= 1n ? 0 : (v - 1n).toString(2).length);
  function compositions(n, k) { if (k === 0) return n === 0 ? 1n : 0n; let c = 1n; for (let i = 1; i <= k - 1; i++) c = c * big(n + i) / big(i); return c; }

  function compress(seq) {
    const alphabet = sortSyms(seq), idx = new Map(alphabet.map((a, i) => [a, i]));
    const counts = alphabet.map(() => 0); for (const x of seq) counts[idx.get(x)]++;
    return { alphabet, counts: counts.slice(), rank: rankOf(seq.map((x) => idx.get(x)), counts) };
  }
  // rank of a sequence of symbol indices with the given counts (counts are used up)
  function rankOf(ix, counts0) {
    const counts = counts0.slice(); let n = ix.length, m = multinomial(counts), r = 0n;
    for (const i of ix) {
      let pre = 0; for (let j = 0; j < i; j++) pre += counts[j];
      const N = big(n);
      r += m * big(pre) / N;
      m = m * big(counts[i]) / N; counts[i]--; n--;
    }
    return r;
  }
  // the sequence of symbol indices with these counts and rank (null if the rank is out of range)
  function unrankOf(counts0, rank) {
    const counts = counts0.slice(); let n = counts.reduce((a, b) => a + b, 0), m = multinomial(counts), r = rank;
    if (r < 0n || r >= m) return null;
    const out = new Array(n);
    for (let p = 0; n > 0; p++) {
      const N = big(n), q = Number(r * N / m);
      let j = 0, pre = 0; while (pre + counts[j] <= q) { pre += counts[j]; j++; }
      r -= m * big(pre) / N;
      m = m * big(counts[j]) / N; counts[j]--; n--;
      out[p] = j;
    }
    return r === 0n ? out : null;
  }
  function decompress(code) {
    const { alphabet, counts, rank } = code;
    if (!Array.isArray(alphabet) || !Array.isArray(counts) || alphabet.length !== counts.length) return null;
    if (counts.some((c) => !Number.isInteger(c) || c < 0)) return null;
    const ix = unrankOf(counts, big(rank)); return ix && ix.map((i) => alphabet[i]);
  }
  function neurons(seq) {
    const alphabet = sortSyms(seq), idx = new Map(alphabet.map((a, i) => [a, i]));
    const counts = alphabet.map(() => 0); for (const x of seq) counts[idx.get(x)]++;
    let n = seq.length, m = multinomial(counts); const out = [];
    seq.forEach((x, p) => { const i = idx.get(x); let pre = 0; for (let j = 0; j < i; j++) pre += counts[j]; const N = big(n); out.push({ position: p + 1, symbol: x, weight: m * big(pre) / N }); m = m * big(counts[i]) / N; counts[i]--; n--; });
    return out;
  }
  const KB = 1.380649e-23;
  const sig4 = (x) => Number(x.toExponential(3));
  const landauer = (bits, kelvin) => sig4(bits * KB * kelvin * Math.log(2));
  const entropyExact = (counts, n) => (n === 0 ? 0 : counts.reduce((h, c) => (c ? h - (c * Math.log(c / n)) / Math.log(2) : h), 0));
  function report(seq) {
    const { alphabet, counts, rank } = compress(seq), n = seq.length, k = alphabet.length, m = multinomial(counts);
    const rb = bitsFor(m), cb = bitsFor(compositions(n, k)), raw = n * bitsFor(big(k));
    const erased = Math.max(0, raw - rb - cb);
    return { n, alphabet, counts, rank, classSize: m, rankBits: rb, compositionBits: cb, rawBits: raw, entropyBits: Math.round(entropyExact(counts, n) * 1000) / 1000, erasedBitsIrreversible: erased, erasedBitsReversible: 0, landauerJoules300K: landauer(erased, 300) };
  }

  // The checks of thermo_prove/3 on every sequence over the alphabet up to maxLen (=< 8):
  // round trip, ranks of each class exactly 0..M-1, neuron sum, entropy bound, no erasure.
  function prove(alphabet0, maxLen) {
    const alphabet = sortSyms(alphabet0);
    if (alphabet.length !== alphabet0.length || alphabet.length < 1 || alphabet.length > 4 || !(maxLen >= 0 && maxLen <= 8)) return { rejected: 'bad_domain' };
    const seqs = []; (function gen(s) { seqs.push(s); if (s.length < maxLen) for (const a of alphabet) gen(s.concat([a])); })([]);
    const classes = new Map();
    for (const s of seqs) {
      const c = compress(s); const back = decompress(c);
      if (!back || back.length !== s.length || back.some((x, i) => x !== s[i])) return { rejected: 'round_trip', witness: s };
      if (neurons(s).reduce((a, x) => a + x.weight, 0n) !== c.rank) return { rejected: 'neuron_sum', witness: s };
      const r = report(s); if (r.rankBits > Math.ceil(entropyExact(r.counts, r.n) - 1e-9)) return { rejected: 'entropy_bound', witness: s };
      const key = JSON.stringify([c.alphabet, c.counts]); if (!classes.has(key)) classes.set(key, []); classes.get(key).push(c.rank);
    }
    for (const [key, rs] of classes) {
      const m = multinomial(JSON.parse(key)[1]); rs.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
      if (big(rs.length) !== m || rs.some((r, i) => r !== big(i))) return { rejected: 'bijection', witness: JSON.parse(key) };
    }
    return { proof: [
      { step: 1, name: 'thermo_round_trip', verified: { domain: [alphabet, maxLen], count: seqs.length } },
      { step: 2, name: 'thermo_bijection', verified: { typeClasses: classes.size, ranks: 'exact' } },
      { step: 3, name: 'thermo_neuron_sum', verified: { domain: [alphabet, maxLen], count: seqs.length } },
      { step: 4, name: 'thermo_entropy_bound', verified: { domain: [alphabet, maxLen], count: seqs.length } },
      { step: 5, name: 'thermo_landauer', erasedBits: 0 }] };
  }

  // ---- the store: a string as blocks of thermo codes, in a byte array ----
  class BitW {
    constructor() { this.bytes = []; this.cur = 0; this.n = 0; }
    bit(b) { this.cur = (this.cur << 1) | b; if (++this.n === 8) { this.bytes.push(this.cur); this.cur = 0; this.n = 0; } }
    bits(v, w) { for (let i = w - 1; i >= 0; i--) this.bit((v >>> i) & 1); }
    bigBits(v, w) { const s = v.toString(2).padStart(w, '0'); for (let i = 0; i < w; i++) this.bit(s.charCodeAt(i) & 1); }
    gamma(v) { const w = v.toString(2).length; for (let i = 1; i < w; i++) this.bit(0); this.bits(v, w); } // v >= 1
    done() { if (this.n) { this.bytes.push(this.cur << (8 - this.n)); } return Uint8Array.from(this.bytes); }
  }
  class BitR {
    constructor(u8, pos) { this.u = u8; this.p = pos * 8; }
    bit() { const b = (this.u[this.p >> 3] >> (7 - (this.p & 7))) & 1; this.p++; return b; }
    bits(w) { let v = 0; for (let i = 0; i < w; i++) v = (v << 1) | this.bit(); return v >>> 0; }
    bigBits(w) { if (!w) return 0n; let s = ''; for (let i = 0; i < w; i++) s += this.bit(); return BigInt('0b' + s); }
    gamma() { let z = 0; while (!this.bit()) z++; let v = 1; for (let i = 0; i < z; i++) v = (v << 1) | this.bit(); return v; }
  }
  const MAGIC = [0x54, 0x48, 0x31]; // "TH1"
  function pack(text, { block = 128 } = {}) {
    const units = []; for (let i = 0; i < text.length; i++) units.push(text.charCodeAt(i));
    const alphabet = sortSyms(units), idx = new Map(alphabet.map((a, i) => [a, i]));
    const w = new BitW();
    MAGIC.forEach((b) => w.bits(b, 8));
    w.gamma(alphabet.length + 1); for (const a of alphabet) w.bits(a, 16);
    w.gamma(block); w.gamma(units.length + 1);
    for (let s = 0; s < units.length; s += block) {
      const ix = units.slice(s, s + block).map((u) => idx.get(u));
      const counts = alphabet.map(() => 0); for (const i of ix) counts[i]++;
      for (const c of counts) w.bit(c ? 1 : 0);
      for (const c of counts) if (c) w.gamma(c);
      const used = counts.filter((c) => c), local = []; const map = []; counts.forEach((c, i) => { if (c) { map[i] = local.length; local.push(i); } });
      const m = multinomial(used);
      w.bigBits(rankOf(ix.map((i) => map[i]), used), bitsFor(m));
    }
    return w.done();
  }
  function unpack(u8) {
    if (!u8 || u8.length < 3 || u8[0] !== MAGIC[0] || u8[1] !== MAGIC[1] || u8[2] !== MAGIC[2]) throw new Error('not a thermo store');
    const r = new BitR(u8, 3);
    const k = r.gamma() - 1, alphabet = []; for (let i = 0; i < k; i++) alphabet.push(r.bits(16));
    const block = r.gamma(), total = r.gamma() - 1;
    const parts = [];
    for (let s = 0; s < total; s += block) {
      const present = alphabet.map(() => r.bit());
      const used = [], local = []; present.forEach((b, i) => { if (b) { used.push(r.gamma()); local.push(alphabet[i]); } });
      const m = multinomial(used);
      const ix = unrankOf(used, r.bigBits(bitsFor(m))); if (!ix) throw new Error('corrupt thermo store');
      parts.push(String.fromCharCode(...ix.map((i) => local[i])));
    }
    const out = parts.join(''); if (out.length !== total) throw new Error('corrupt thermo store');
    return out;
  }
  const toBase64 = (u8) => (typeof Buffer !== 'undefined' ? Buffer.from(u8).toString('base64') : btoa(String.fromCharCode(...u8)));
  const fromBase64 = (s) => (typeof Buffer !== 'undefined' ? new Uint8Array(Buffer.from(s, 'base64')) : Uint8Array.from(atob(s), (c) => c.charCodeAt(0)));

  P.thermo = { compress, decompress, neurons, report, prove, landauer, multinomial, pack, unpack, toBase64, fromBase64 };
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));

/* interp.js - the pl2detlog interpreter: runs SWI-Prolog programs (and swipl command lines) on the
   fastest exact route, so that a program needs no SWI-Prolog, and runs faster where it has one.

   For each goal it has these routes:
     C        pl2detlog's C export, compiled by a C compiler where the host has one (nativeC, in
              Node) and run as a process; in a web page, the same analysis compiled to JavaScript
              (the native tier). Exact for calls that meet the type contract (ground inputs, fresh
              outputs); its answers must equal the MNN route's on the first run.
     MNN      the proved Detlog MNN rewrite (src/convert.js, src/rewrite.js), run by the JIT.
     Prolog   the reference engine with SWI-Prolog's library (src/swi.js): for what the conversion
              can't keep exact (database updates, files and streams, conversion errors, a round
              trip that reports a change), and whenever it is faster.
   The first run of a goal times the routes that apply, checks they agree, and keeps the fastest;
   the choice and the conversion are kept in a store (cache) so that the next process starts there.
   Where the store holds text (the conversion, the choice), it is kept as thermodynamic compression
   MNN codes (src/thermo.js) when that is smaller and decoding it is not slower than redoing the
   conversion; otherwise as plain JSON.

   Point 1 (a bound output is computed, then unified) and the rest of the hybrid's rules follow the
   Detlog MNN hybrid (github.com/luciangreen/detlogmnn, web/lib/hybrid.js).

   swipl command lines (runArgs): files are consulted (consult/include/use_module/ensure_loaded of
   files are read in; library modules are built in), load directives run, initialization/1 goals run
   after loading, -g goals run in order, initialization(main, main) runs and halts, and the exit code
   is SWI-Prolog's (1 when a goal fails, 2 when it raises an error, halt(N) gives N). A program that
   needs what only SWI-Prolog has (term or goal expansion, modules' private predicates, foreign
   libraries) is reported as such, so that a host with swipl can hand it over (needsSwi). */
(function (P) {
  'use strict';
  const D = (t) => P.deref(t);
  const VERSION = 'pl2detlog-interp-1';

  // ---------------------------------------------------------------- hashing (store keys)
  function hash(s) {
    let h1 = 0x811c9dc5, h2 = 0x01000193 ^ s.length;
    for (let i = 0; i < s.length; i++) { const c = s.charCodeAt(i); h1 = Math.imul(h1 ^ c, 16777619); h2 = Math.imul(h2 ^ c, 2246822519) ^ (h2 >>> 13); }
    return (h1 >>> 0).toString(16).padStart(8, '0') + (h2 >>> 0).toString(16).padStart(8, '0');
  }

  // ---------------------------------------------------------------- terms
  const conjList = (g) => { g = D(g); return g.t === 'c' && g.f === ',' && g.a.length === 2 ? conjList(g.a[0]).concat(conjList(g.a[1])) : [g]; };
  const occurs = (v, t) => { t = D(t); return t === v || t.t === 'c' && t.a.some((x) => occurs(v, x)); };
  const keyOf = (g) => { g = D(g); return g.t === 'c' ? g.f + '/' + g.a.length : g.t === 'a' ? g.n + '/0' : null; };
  const isIte = (g) => { g = D(g); return g.t === 'c' && g.f === ';' && g.a.length === 2 && D(g.a[0]).t === 'c' && D(g.a[0]).f === '->' && D(g.a[0]).a.length === 2; };
  const isCut = (g) => { g = D(g); return g.t === 'a' && g.n === '!'; };

  // every predicate a goal can reach (subterms count, so goals inside findall/3 and call/N do)
  function reaches(prog, term) {
    const seen = new Set(), todo = [];
    const visit = (t) => { t = D(t); const k = keyOf(t); if (k && !seen.has(k)) { seen.add(k); if (prog.preds.has(k)) todo.push(k); } if (t.t === 'c') t.a.forEach(visit); };
    visit(term);
    while (todo.length) for (const cl of prog.preds.get(todo.pop())) visit(cl.body);
    return seen;
  }
  const DB = /^(assert[az]?|retract(all)?|abolish)\/\d+$/;
  // builtins whose effects only the Prolog route keeps: streams, files, the process, messages, state
  const EFFECTS = new Set(['open/3', 'open/4', 'close/1', 'close/2', 'read_line_to_string/2', 'read_line_to_codes/2', 'read_string/3', 'read_string/5', 'read_term/2', 'read_term/3', 'read/1', 'read/2',
    'read_file_to_string/3', 'read_file_to_codes/3', 'read_file_to_terms/3', 'json_read_dict/2', 'json_read_dict/3', 'json_read/2', 'json_write_dict/2', 'json_write_dict/3', 'json_write/2', 'json_write/3',
    'write/2', 'writeln/2', 'writeq/2', 'print/2', 'nl/1', 'tab/2', 'put_char/2', 'format/3', 'write_term/3', 'print_message/2', 'halt/0', 'halt/1', 'exists_file/1', 'exists_directory/1', 'directory_files/2',
    'delete_file/1', 'make_directory/1', 'working_directory/2', 'getenv/2', 'shell/1', 'shell/2', 'current_prolog_flag/2', 'absolute_file_name/2', 'absolute_file_name/3', 'get_char/1', 'get_char/2',
    'peek_char/2', 'get_code/2', 'at_end_of_stream/0', 'at_end_of_stream/1', 'consult/1', 'load_files/2', 'use_module/1', 'use_module/2', 'ensure_loaded/1', 'nb_setval/2', 'b_setval/2', 'nb_getval/2', 'b_getval/2',
    'clause/2', 'current_predicate/1', 'current_predicate/2', 'predicate_property/2', 'random/1', 'random_between/3', 'get_time/1', 'statistics/2', 'setarg/3', 'nb_setarg/3', 'tmp_file/2', 'time/1', 'prolog_load_context/2', 'stack_trace/0']);

  // builtins that look at variables themselves (identity, order, binding): the packets of the
  // compiled Detlog copy a call's arguments, so a call that compares variables it was given is kept
  // on the Prolog route (per call; a whole goal is compared with Prolog on its first run)
  const VARSENS = new Set(['==/2', '\\==/2', 'var/1', 'nonvar/1', '@</2', '@>/2', '@=</2', '@>=/2', 'compare/3', 'copy_term/2', 'term_variables/2', '=@=/2', '\\=@=/2', 'ground/1', 'sort/2', 'msort/2', 'sort/4', 'predsort/3', 'setof/3', 'bagof/3', 'unify_with_occurs_check/2', 'numbervars/3', 'numbervars/4', 'subsumes_term/2', 'term_to_atom/2', 'term_string/2', 'term_string/3', 'format/2', 'format/3', 'with_output_to/2', 'b_setval/2', 'b_getval/2', 'nb_getval/2', 'nb_setval/2', 'list_to_set/2', 'is_set/1', 'sort_unique/2', 'keysort/2']);

  // ---------------------------------------------------------------- point 1 (see detlogmnn)
  function steadfast(prog, k, i, assume = new Set()) {
    const id = k + '#' + i;
    if (assume.has(id)) return { ok: true, why: 'recursive call (proved by induction)' };
    const cls = prog.preds.get(k);
    if (!cls || !cls.length) return { ok: false, why: k + ' has no clauses here' };
    if (prog.dynamic.has(k)) return { ok: false, why: k + ' is dynamic' };
    const seen = new Set(assume).add(id), reasons = [];
    for (const [ci, cl] of cls.entries()) {
      const head = D(cl.head), V = D(head.a[i]);
      if (V.t !== 'v') return { ok: false, why: 'clause ' + (ci + 1) + ' of ' + k + ' has a value in argument ' + (i + 1) };
      if (head.a.some((x, j) => j !== i && occurs(V, x))) return { ok: false, why: 'clause ' + (ci + 1) + ' of ' + k + ' shares argument ' + (i + 1) + ' with another argument' };
      const r = bodyOk(prog, conjList(cl.body), V, seen);
      if (!r.ok) return { ok: false, why: 'clause ' + (ci + 1) + ' of ' + k + ': ' + r.why };
      reasons.push(r.why);
    }
    return { ok: true, why: [...new Set(reasons)].join('; ') };
  }
  function bodyOk(prog, goals, V, seen) {
    if (!goals.length) return { ok: false, why: 'the output is never computed' };
    const last = D(goals[goals.length - 1]);
    const cut = goals.map(isCut).lastIndexOf(true);
    if (cut >= 0) {
      if (goals.slice(0, cut).some((g) => occurs(V, g))) return { ok: false, why: 'the output is used before the cut' };
      const r = bodyOk(prog, goals.slice(cut + 1), V, seen);
      return r.ok ? { ok: true, why: 'cut first (D), then ' + r.why } : r;
    }
    if (goals.slice(0, -1).some((g) => occurs(V, g))) return { ok: false, why: 'the output is used before its value is computed' };
    if (last.t === 'c' && last.a.length === 2 && (last.f === '=' || last.f === 'is')) {
      const [l, r] = last.a.map(D);
      if (l === V && !occurs(V, r)) return { ok: true, why: 'computed then bound (A: ' + last.f + ')' };
      if (last.f === '=' && r === V && !occurs(V, l)) return { ok: true, why: 'computed then bound (A: =)' };
      return { ok: false, why: 'the output is compared, not just bound' };
    }
    if (isIte(last)) {
      const [c, t] = D(last.a[0]).a; const e = last.a[1];
      if (occurs(V, c)) return { ok: false, why: 'the output is used in a condition' };
      const rt = bodyOk(prog, conjList(t), V, seen); if (!rt.ok) return rt;
      const re = bodyOk(prog, conjList(e), V, seen); if (!re.ok) return re;
      return { ok: true, why: 'committed, then each branch bound (B)' };
    }
    const k = keyOf(last);
    if (k && prog.preds.has(k)) {
      const at = last.a.map(D).reduce((acc, x, j) => (x === V ? acc.concat([j]) : occurs(V, x) ? acc.concat([-1]) : acc), []);
      if (at.length !== 1 || at[0] < 0) return { ok: false, why: 'the output is passed to ' + k + ' other than as one whole argument' };
      const r = steadfast(prog, k, at[0], seen);
      return r.ok ? { ok: true, why: 'passed on (C: ' + k + ' argument ' + (at[0] + 1) + ')' } : { ok: false, why: r.why };
    }
    return { ok: false, why: k ? 'the last goal ' + k + ' is not a program predicate' : 'the last goal is not a call' };
  }
  function pointOne(prog, queryText) {
    const q = P.readTerm(queryText), g = D(q.term), k = keyOf(g);
    if (!k || g.t !== 'c' || !prog.preds.has(k)) return { text: queryText, outputs: [] };
    const args = g.a.map(D), outputs = [], parts = [], nm = P.namer();
    const shown = args.map((x) => P.show(x, { quoted: true, varName: (v) => { const f = q.vars.find(([, w]) => D(w) === v); return f ? f[0] : nm(v); } }));
    args.forEach((x, i) => {
      if (x.t === 'v' || !P.isGround(x)) return;
      const s = steadfast(prog, k, i); if (!s.ok) return;
      outputs.push({ arg: i + 1, why: s.why }); parts.push('_O' + (i + 1) + ' = ' + shown[i]); shown[i] = '_O' + (i + 1);
    });
    if (!outputs.length) return { text: queryText, outputs };
    return { text: P.show(P.Atom(g.f), { quoted: true }) + '(' + shown.join(', ') + '), ' + parts.join(', '), outputs };
  }

  // ---------------------------------------------------------------- loading SWI-Prolog files
  const LOADERS = new Set(['consult', 'include', 'ensure_loaded', 'use_module', 'load_files', 'reexport']);
  const DROP = new Set(['module', 'set_prolog_flag', 'license', 'encoding', 'style_check', 'use_foreign_library', 'meta_predicate', 'module_transparent', 'public', 'multifile', 'table', 'noprofile', 'create_prolog_flag', 'expects_dialect']);
  const NEEDS_SWI = new Set(['term_expansion/4', 'goal_expansion/4', 'prolog_load_file/2']);
  const fileSpec = (t) => { t = D(t); if (t.t === 'c' && t.f === 'library') return { library: true }; if (t.t === 'c' && t.a.length === 2 && t.f === ':') return fileSpec(t.a[1]); if (t.t === 'c' && t.f === '/' && t.a.length === 2) { const a = fileSpec(t.a[0]), b = fileSpec(t.a[1]); return { path: a.path + '/' + b.path }; } if (t.t === 'c' && t.a.length === 1) return { alias: t.f, path: P.textOf(t.a[0]) }; return { path: P.textOf(t) }; };
  const dirOf = (p) => { const i = p.lastIndexOf('/'); return i < 0 ? '' : i === 0 ? '/' : p.slice(0, i); };

  // The program text with every file it loads read in (each once), and what to run after loading.
  function loadFiles(io, files, opts = {}) {
    const st = { seen: new Set(), parts: [], loadGoals: [], init: [], initMain: null, needsSwi: [], missing: [], files: [] };
    for (const f of files) loadFile(io, f, st, io.cwd || '');
    st.src = st.parts.join('\n');
    if (opts.prelude !== false) st.src += '\n% ---- SWI-Prolog library (pl2detlog src/swi.js) ----\n' + P.SWI_PRELUDE;
    return st;
  }
  function findFile(io, base, name) {
    const cands = [];
    const p = P.joinPath(base, name);
    cands.push(p); if (!/\.\w+$/.test(name)) cands.push(p + '.pl', p + '.pro', p + '.prolog');
    for (const c of cands) { const s = io.stat ? io.stat(c) : (io.readFile(c) != null ? 'file' : null); if (s === 'file') return c; }
    return null;
  }
  // the text of a clause term, with its variables' names where the source gave them
  const clauseText = (t, vars) => {
    const names = new Map((vars || []).map(([n, v]) => [D(v), n])), nm = P.namer();
    const varName = (v) => names.get(v) || nm(v);
    t = D(t);
    return (t.t === 'c' && t.f === ':-' && t.a.length === 1 ? ':- ' + P.show(t.a[0], { quoted: true, varName, prec: 1199 }) + '.' : P.showClause(t, { varName })) + '\n';
  };
  const definesExpansion = (t) => { t = D(t); if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = D(t.a[0]); while (t.t === 'c' && t.f === ':' && t.a.length === 2) t = D(t.a[1]); const k = keyOf(t); return k === 'term_expansion/2' || k === 'goal_expansion/2'; };
  // an engine on the program loaded so far, to run term_expansion/2 and goal_expansion/2 (Starlog's)
  function expander(io, st) {
    if (!st.hooks) return null;
    if (st.expander && st.expander.at === st.parts.length) return st.expander.e;
    let prog;
    try { prog = P.loadProgram(st.parts.join('\n') + '\n' + P.SWI_PRELUDE); } catch (e) { return null; }
    for (const [M, k] of st.privates || []) P.notePrivates(prog, M, [k]);
    prog.moduleFiles = new Map(st.moduleFiles || []);
    const e = new P.Engine(prog, { io, stepLimit: 1e8 });
    st.expander = { at: st.parts.length, e };
    return e;
  }
  function loadFile(io, path, st, base) {
    const full = findFile(io, base, path) || (io.cwd && base !== io.cwd ? findFile(io, io.cwd, path) : null);
    if (!full) { st.missing.push(path); return; }
    if (st.seen.has(full)) return;
    st.seen.add(full); st.files.push(full);
    const text = io.readFile(full);
    const dir = dirOf(full);
    // 1. read the clauses in order: operators and the files a clause loads take effect at once, so
    //    what follows is read with them (as SWI-Prolog reads a file)
    const items = []; let rest = text;
    for (;;) {
      const cl = P.nextClauseText(rest); if (cl === null) break;
      rest = rest.slice(cl.length);
      let r = null, err = null; try { r = P.readTerm(cl); } catch (e) { err = e; }
      const item = { text: cl, r, err };
      items.push(item);
      if (!r) continue;
      const t = D(r.term);
      if (!(t.t === 'c' && t.f === ':-' && t.a.length === 1)) continue;
      const d = D(t.a[0]), n = d.t === 'c' ? d.f : d.t === 'a' ? d.n : '';
      P.applyOpDirective(d);
      if (d.t === 'c' && LOADERS.has(n)) {
        for (const x of (P.listToArray(d.a[0]) || [d.a[0]])) {
          const sp = fileSpec(x);
          if (sp.library || sp.alias && sp.alias !== 'library' && !findFile(io, dir, sp.path)) continue; // built in (src/swi.js)
          loadFile(io, sp.path, st, dir);
        }
        item.loaded = true;
      } else if (d.t === 'c' && d.f === '.') { for (const x of P.listToArray(d) || []) loadFile(io, fileSpec(x).path, st, dir); item.loaded = true; }
    }
    // 2. a module's predicates are renamed (src/swi.js)
    const md = (function () { for (const x of items) { if (!x.r) return null; const d = D(x.r.term); if (!(d.t === 'c' && d.f === ':-' && d.a.length === 1)) return null; const g = D(d.a[0]); if (g.t === 'c' && g.f === 'module' && g.a.length === 2) return g; } return null; })();
    const extra = [];
    if (md) {
      const M = P.textOf(md.a[0]);
      const ren = P.renameModule(items.map((x) => x.r ? x.r.term : P.Atom('true')), M, P.moduleExports(md));
      st.privates = (st.privates || []).concat(ren.privates.map((k) => [M, k]));
      (st.moduleFiles = st.moduleFiles || []).push([M, full]);
      items.forEach((x, i) => { if (x.r && !x.loaded) x.r = { term: D(ren.terms[i]), vars: x.r.vars, renamed: true }; });
      st.forwarded = st.forwarded || new Set();
      for (const fw of ren.forwarders) if (!st.forwarded.has(fw.key)) { st.forwarded.add(fw.key); extra.push({ text: P.showClause(fw.clause) + '\n', r: { term: fw.clause, vars: [], renamed: true } }); }
    }
    // 3. each clause, expanded by term_expansion/goal_expansion where the program has them, is kept
    st.parts.push('% ---- ' + full + ' ----');
    const defines = items.some((x) => x.r && definesExpansion(x.r.term));
    for (const item of items.concat(extra)) {
      if (!item.r) { st.parts.push(item.text); continue; }
      if (item.loaded) { st.parts.push('% ' + item.text.trim().replace(/\n/g, ' ')); continue; }
      let terms = [{ term: item.r.term, vars: item.r.vars, text: item.r.renamed ? null : item.text }];
      const ex = definesExpansion(item.r.term) ? null : expander(io, st);
      if (ex) {
        const out = P.expandClauses(ex, [{ term: item.r.term, vars: item.r.vars }]);
        if (out.length !== 1 || P.variantKey(out[0].term) !== P.variantKey(item.r.term)) terms = out.map((o) => ({ term: o.term, vars: o.vars, text: null }));
      }
      for (const { term, vars, text: tx } of terms) emit(io, st, term, tx || clauseText(term, vars), dir);
    }
    if (rest.trim()) st.parts.push(rest);
    if (defines) { st.hooks = true; st.expander = null; }
  }
  function emit(io, st, term, cl, dir) {
    const t = D(term);
    if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
      const d = D(t.a[0]), k = keyOf(d), n = d.t === 'c' ? d.f : d.t === 'a' ? d.n : '';
      if (n === 'op') { st.parts.push(cl); return; }
      if (n === 'initialization') {
        const how = d.a.length === 2 ? P.textOf(d.a[1]) : 'now';
        if (how === 'main') st.initMain = P.show(d.a[0], { quoted: true }); else st.init.push(P.show(d.a[0], { quoted: true }));
        st.parts.push('% ' + cl.trim().replace(/\n/g, ' '));
        return;
      }
      if (DROP.has(n)) { st.parts.push('% ' + cl.trim().replace(/\n/g, ' ')); return; }
      if (n === 'dynamic' || n === 'discontiguous') { st.parts.push(cl); return; }
      if (n === 'begin_tests' || n === 'end_tests') { st.unit = n === 'begin_tests' ? P.textOf(d.a[0]) : null; st.parts.push('% ' + cl.trim().replace(/\n/g, ' ')); if (n === 'begin_tests' && d.a.length === 2) st.parts.push(P.show(P.Cmp('$plunit_unit', [d.a[0], d.a[1]]), { quoted: true, ignoreOps: false }) + '.'); return; }
      // any other directive runs when the files are loaded, in order
      st.loadGoals.push(P.show(d, { quoted: true }));
      st.parts.push('% ' + cl.trim().replace(/\n/g, ' '));
      if (k && /^(assert|retract)/.test(k)) st.dynamicLoad = true;
      return;
    }
    // plunit: test(Name) and test(Name, Options) between begin_tests(Unit) and end_tests(Unit)
    if (st.unit) {
      let h = t, b = P.Atom('true');
      if (t.t === 'c' && t.f === ':-' && t.a.length === 2) { h = D(t.a[0]); b = t.a[1]; }
      if (h.t === 'c' && (h.f === 'test' || /:test$/.test(h.f)) && (h.a.length === 1 || h.a.length === 2)) {
        const ut = P.Cmp(':-', [P.Cmp('$plunit_test', [P.Atom(st.unit), h.a[0], h.a.length === 2 ? h.a[1] : P.NIL, P.Int(++st.testSeq || (st.testSeq = 1))]), b]);
        st.parts.push(clauseText(ut, []));
        return;
      }
    }
    if (t.t === 'c' && t.f === ':-' && t.a.length === 2) { const hk = keyOf(t.a[0]); if (NEEDS_SWI.has(hk)) st.needsSwi.push('defines ' + hk); }
    else if (NEEDS_SWI.has(keyOf(t))) st.needsSwi.push('defines ' + keyOf(t));
    st.parts.push(cl);
  }

  // ---------------------------------------------------------------- the interpreter
  const sameAnswers = (a, b) => JSON.stringify(a.events) === JSON.stringify(b.events);
  function time(f, minMs = 20, maxReps = 50) { let reps = 0; const t0 = P.now(); let r; do { r = f(); reps++; } while (P.now() - t0 < minMs && reps < maxReps); return { r, ms: (P.now() - t0) / reps }; }
  function limit(steps, ms) {
    let n = 0, timedOut = false; const deadline = P.now() + ms;
    return { valueOf() { if ((++n & 4095) === 0 && P.now() > deadline) timedOut = true; return timedOut ? -1 : steps; }, toString() { return timedOut ? 'time limit ' + ms / 1000 + ' s' : String(steps); } };
  }
  const tidy = (e) => (e ? String(e).replace(/^step limit \(time limit ([\d.]+ s)\) exceeded$/, 'time limit ($1) exceeded') : e);
  // the events up to the first answer (a -g goal runs once)
  const firstOnly = (r) => { const ev = []; for (const e of r.events) { ev.push(e); if (e.k === 'row') break; } return Object.assign({}, r, { events: ev, answers: r.answers.slice(0, 1), output: ev.filter((e) => e.k === 'out').map((e) => e.text).join('') }); };

  // smallTerms(ts, n): the terms have at most n cells in all
  function smallTerms(ts, n) {
    const st = ts.slice();
    while (st.length) { const t = D(st.pop()); if (t.t === 'c') { if ((n -= t.a.length) < 0) return false; for (const x of t.a) st.push(x); } }
    return true;
  }

  // Prolog is kept for a goal when it takes this many times less than the Detlog MNN and C route
  const PROLOG_FASTER = 2, PROLOG_MIN_GAIN = 0.5;

  class Interpreter {
    // opts: io (see src/swi.js), store ({ get(key) -> string|null, set(key, string) }), nativeC (Node:
    // { compile(code) -> handle|null, run(handle, args) -> { stdout, stderr, status, ms } }),
    // stepLimit, timeLimitMs, checked
    constructor(opts = {}) {
      this.io = opts.io || P.defaultIO || {};
      this.store = opts.store || null; this.nativeC = opts.nativeC || null;
      this.stepLimit = opts.stepLimit || 5e7; this.timeLimitMs = opts.timeLimitMs || 60000; this.checked = !!opts.checked;
      this.log = opts.log || null; this.noAccel = !!opts.noAccel;
      this.setProgram('');
    }
    setProgram(src, meta = {}) {
      this.src = src; this.meta = meta; this.plans = new Map(); this.live = null; this.globals = new Map();
      this.srcKey = hash(VERSION + '\0' + src);
      const was = P.SWI_WRITE; P.SWI_WRITE = true;
      try { this.prog = this.freshProgram(); this.loadError = null; } catch (e) { this.prog = P.loadProgram(''); this.loadError = e.message; } finally { P.SWI_WRITE = was; }
      this.dynamic = !!meta.dynamicLoad || /\b(assert[az]?|retract(all)?|abolish)\s*\(/.test(src);
      if (this.installTime) this.installTime();
    }
    // the program as loaded, with its modules' private names and files (a run that changes the
    // database starts from a fresh copy)
    freshProgram() {
      const prog = P.loadProgram(this.src);
      for (const [M, k] of this.meta.privates || []) P.notePrivates(prog, M, [k]);
      prog.moduleFiles = new Map(this.meta.moduleFiles || []);
      return prog;
    }
    loadFiles(files, opts) { const st = loadFiles(this.io, files, opts); this.setProgram(st.src, st); return st; }

    // ---- the store
    remember(key, obj, reconvertMs) {
      if (!this.store) return;
      const json = JSON.stringify(obj);
      let rec = 'j' + json;
      try {
        const u8 = P.thermo.pack(json); const b64 = P.thermo.toBase64(u8);
        const t0 = P.now(); P.thermo.unpack(u8); const unpackMs = P.now() - t0;
        // thermo codes where they are smaller and decoding them is not slower than redoing the work
        if (b64.length + 1 < rec.length && unpackMs <= reconvertMs) rec = 't' + b64;
      } catch (e) { /* plain JSON */ }
      try { this.store.set(key, rec); } catch (e) { /* a full store keeps nothing */ }
    }
    recall(key) {
      if (!this.store) return null;
      let rec; try { rec = this.store.get(key); } catch (e) { return null; }
      if (!rec) return null;
      try { return JSON.parse(rec[0] === 't' ? P.thermo.unpack(P.thermo.fromBase64(rec.slice(1))) : rec.slice(1)); } catch (e) { return null; }
    }

    // ---- the plan for a goal: which routes apply and why
    plan(goalText) {
      goalText = goalText.trim().replace(/\.\s*$/, '');
      if (this.plans.has(goalText)) return this.plans.get(goalText);
      const plan = { goal: goalText, notes: [], key: this.srcKey + '-' + hash(goalText) };
      this.plans.set(goalText, plan);
      if (this.loadError) { plan.route = 'Prolog'; plan.why = 'the program has a syntax error: ' + this.loadError; return plan; }
      const saved = this.recall(plan.key);
      const t0 = P.now();
      const p1 = pointOne(this.prog, goalText);
      plan.runAs = p1.text;
      let reached = new Set();
      try { reached = reaches(this.prog, P.readTerm(p1.text).term); } catch (e) { plan.notes.push(e.message); }
      const effects = [...reached].filter((k) => DB.test(k) || EFFECTS.has(k) && !pureUses(this.prog, p1.text, k) || this.prog.dynamic.has(k));
      if (this.dynamic && [...reached].some((k) => this.prog.preds.has(k))) effects.push('the program changes its clauses as it loads');
      if (effects.length) { plan.route = 'Prolog'; plan.why = 'it uses ' + effects.slice(0, 4).join(', ') + ', whose effects only the Prolog route keeps'; return plan; }
      let conv = saved && saved.conv;
      if (!conv) {
        try { conv = P.convert(this.src, { mnn: true, s2a: false, queries: [p1.text] }); } catch (e) { plan.notes.push('conversion: ' + e.message); }
        if (conv && !conv.errors.length && conv.queries && conv.queries[0] && !conv.queries[0].error) {
          try {
            const back = P.backConvert(conv.text);
            const all = P.changeWarnings(this.src, back.text, back).filter((w) => reached.has(w.pred));
            const changes = all.filter((w) => w.kind === 'removed' || w.kind === 'error' || w.kind === 'added' && reached.has(w.pred));
            if (changes.length) conv = { changed: changes.map((c) => c.msg || String(c)) };
          } catch (e) { conv = { changed: ['back-conversion: ' + e.message] }; }
        }
      }
      if (!conv || conv.errors && conv.errors.length || !conv.queries || !conv.queries[0] || conv.queries[0].error) {
        plan.route = 'Prolog'; plan.why = conv && conv.changed ? 'the round trip back to Prolog reports a change' : 'the conversion has errors';
        if (conv && conv.errors) plan.notes.push(...conv.errors.map((x) => (x && x.msg ? (x.pred ? x.pred + ": " : "") + x.msg : String(x)))); if (conv && conv.changed) plan.notes.push(...conv.changed);
      } else {
        plan.conv = { text: conv.text, source: conv.source, queries: conv.queries.map((q) => ({ pred: q.pred, vars: q.vars, text: q.text })), errors: [] };
        plan.q = plan.conv.queries[0];
        plan.detlog = P.loadProgram(conv.text);
        try { plan.detlog.pairwiseSource = P.loadProgram(conv.source); } catch (e) { /* the JIT permutes in full */ }
      }
      plan.analysisMs = P.now() - t0;
      if (saved && saved.pick) { plan.pick = saved.pick; plan.why = saved.why; plan.timing = saved.timing; plan.fromStore = true; }
      return plan;
    }
    save(plan) {
      const obj = { v: VERSION, goal: plan.goal, pick: plan.pick, why: plan.why, timing: plan.timing };
      if (plan.conv) obj.conv = plan.conv;
      this.remember(plan.key, obj, plan.analysisMs || 0);
    }

    // ---- per call: inside the Prolog route, a call of a predicate whose every reachable clause
    // converted (and that reaches no effect the packet can't carry) can run on the compiled Detlog
    // MNN instead (the C route's JavaScript where its type contract holds, checked). Its first calls
    // run both ways: the answers (and output) must be the same, and the faster way is kept.
    prepareAccel() {
      if (this.acc !== undefined) return this.acc;
      this.acc = null;
      if (this.loadError || this.noAccel) return null;
      let conv; try { conv = P.convert(this.src, { mnn: true, s2a: false, queries: [] }); } catch (e) { return null; }
      const bad = new Set(conv.errors.map((x) => x.pred).filter(Boolean));
      // the predicates the program may assert into: unknown targets turn per-call routes off
      const targets = new Set(); let anyTarget = false;
      for (const k of this.prog.order) for (const cl of this.prog.preds.get(k)) (function walk(t) { t = D(t); if (t.t !== 'c') return; if (DB.test(t.f + '/' + t.a.length)) { let h = D(t.a[0]); if (h.t === 'c' && h.f === ':-') h = D(h.a[0]); const hk = keyOf(h); if (hk && h.t !== 'v') targets.add(hk); else anyTarget = true; } t.a.forEach(walk); })(cl.body);
      if (anyTarget) return null;
      const ok = new Map();
      const pure = (k, stack = new Set()) => {
        if (ok.has(k)) return ok.get(k);
        if (stack.has(k)) return true;
        stack.add(k);
        let r = !bad.has(k) && !targets.has(k) && !this.prog.dynamic.has(k);
        if (r) for (const cl of this.prog.preds.get(k)) {
          const seen = new Set();
          (function walk(t) { t = D(t); const tk = keyOf(t); if (tk && !seen.has(tk)) { seen.add(tk); } if (t.t === 'c') t.a.forEach(walk); })(cl.body);
          for (const tk of seen) {
            if (DB.test(tk) || VARSENS.has(tk) || EFFECTS.has(tk) && !pureUses(this.prog, P.show(cl.body, { quoted: true }), tk)) { r = false; break; }
            if (this.prog.preds.has(tk) && tk !== k && !pure(tk, stack)) { r = false; break; }
          }
          if (!r) break;
        }
        stack.delete(k); ok.set(k, r); return r;
      };
      const keys = this.prog.order.filter((k) => this.prog.preds.get(k).length && !k.startsWith('$') && pure(k));
      if (!keys.length) return null;
      const was = [P.DETLOG_NATIVE, P.DETLOG_CHECKED];
      P.DETLOG_NATIVE = true; P.DETLOG_CHECKED = true; // the compiled program keeps the checked native tier
      let det;
      try { det = P.loadProgram(conv.text); P.detlogCall(det, keys[0].replace(/\/(\d+)$/, (m, n) => '__cp/' + (+n + 1)), [], {}); } catch (e) { /* compiled lazily */ }
      finally { [P.DETLOG_NATIVE, P.DETLOG_CHECKED] = was; }
      if (!det) return null;
      this.acc = { det, info: new Map(keys.map((k) => [k, { state: 'try', calls: 0, samples: 0, jitMs: 0, prologMs: 0, fails: 0 }])) };
      return this.acc;
    }
    // a sampled call's budget, on either route: more steps than this and the predicate stays on Prolog
    accelFn() {
      const SAMPLE_STEPS = 200000;
      const acc = this.prepareAccel(); if (!acc) return null;
      const self = this;
      return function (k, g, eng) {
        const info = acc.info.get(k); if (!info || info.state === 'prolog' || info.busy) return null;
        if (info.state === 'try' && ++info.calls < 20) return null; // only predicates called often are tried
        const n = g.t === 'c' ? g.a.length : 0, args = n ? g.a.slice() : [];
        // the compiled call copies its arguments (a packet's rows are copies): a call on a large term
        // (key(Clause, K) on a whole clause, say) stays on Prolog
        if (!smallTerms(args, 300)) return null;
        const R = P.Var('R');
        const call = (Rv) => {
          const was = [P.DETLOG_NATIVE, P.DETLOG_CHECKED]; P.DETLOG_NATIVE = true; P.DETLOG_CHECKED = true;
          try { return P.detlogCall(acc.det, k.replace(/\/(\d+)$/, (m, a) => '__cp/' + (+a + 1)), args.concat([Rv]), { stepLimit: info.state === 'try' ? SAMPLE_STEPS : 5e6 }); }
          catch (e) { return null; }
          finally { [P.DETLOG_NATIVE, P.DETLOG_CHECKED] = was; }
        };
        // the first call compiles: it is not timed
        if (info.state === 'try' && !info.warm) { info.warm = true; const W = P.Var('W'), m0 = eng.mark(); call(W); eng.undo(m0); }
        let t0 = P.now();
        const res = call(R);
        const jitMs = P.now() - t0;
        if (!res || !res.ok) { if (++info.fails > 2) info.state = 'prolog'; return null; }
        const items = P.listToArray(R) || [];
        // on the compiled route, calls 2, 4, 8, 16, .. are checked again (a few samples can miss a case)
        const recheck = info.state === 'jit' && ((info.jitCalls = (info.jitCalls || 0) + 1) & (info.jitCalls - 1)) === 0;
        if (info.state === 'try' || recheck) {
          // the same call on the Prolog route, all its answers, its output caught
          info.busy = true;
          // within a budget: a call with many answers (a search run under once/1, say) stays on Prolog
          const saveOut = eng.out, saveOn = eng.onOut, mark = eng.mark(), outer = eng.stepLimit; eng.out = ''; eng.onOut = null;
          const sols = []; let perr = null; t0 = P.now();
          eng.stepLimit = eng.steps + SAMPLE_STEPS;
          try { eng.solve(g, () => { sols.push({ out: eng.out, row: P.show(P.Cmp('e', args), { quoted: true, varName: P.namer() }) }); eng.out = ''; return true; }); } catch (e) { perr = e; }
          eng.stepLimit = outer;
          const prologMs = P.now() - t0, tail = eng.out;
          eng.out = saveOut; eng.onOut = saveOn; eng.undo(mark); info.busy = false;
          if (perr) { if (perr.halt) throw perr; if (perr instanceof P.LimitError) void (eng.steps > outer); info.state = 'prolog'; return null; }
          // the packet as the same events
          const mine = []; let pend = '';
          for (const it of items) { const x = D(it); if (x.t === 'c' && x.f === 'out') { pend += P.textOf(x.a[0]); continue; } const m2 = eng.mark(); const vals = P.listToArray(x.a[0]); let row = null; if (vals && vals.length === n && args.every((a, i) => eng.unify(a, vals[i]))) row = P.show(P.Cmp('e', args), { quoted: true, varName: P.namer() }); eng.undo(m2); if (row !== null) { mine.push({ out: pend, row }); pend = ''; } }
          const same = JSON.stringify(mine) === JSON.stringify(sols) && pend === tail;
          if (!same) { if (self.debugAccel) self.debugAccel(k, P.show(g, { quoted: true }), mine, sols, pend, tail); info.state = 'prolog'; if (self.log) self.log({ plan: { goal: k }, route: 'Prolog', why: 'per call: the compiled Detlog gave other answers' }); return null; }
          if (info.state === 'try') {
            info.jitMs += jitMs; info.prologMs += prologMs;
            if (++info.samples >= 3 && !self.debugAccel) info.state = info.jitMs < info.prologMs ? 'jit' : 'prolog';
          }
        }
        return (function* () {
          let rowsLeft = 0; for (const it of items) { const x = D(it); if (!(x.t === 'c' && x.f === 'out')) rowsLeft++; }
          for (let i = 0; i < items.length; i++) {
            const x = D(items[i]);
            if (x.t === 'c' && x.f === 'out') { eng.write(P.textOf(x.a[0])); continue; }
            rowsLeft--;
            const vals = P.listToArray(x.a[0]); const m = eng.mark();
            if (vals && vals.length === n && args.every((a, j) => eng.unify(a, vals[j]))) {
              const restOut = items.slice(i + 1).some((y) => { y = D(y); return y.t === 'c' && y.f === 'out'; });
              if (!rowsLeft && !restOut) { yield 'last'; return; }
              yield;
            }
            eng.undo(m);
          }
        })();
      };
    }

    // ---- the routes
    // stream: write output as it is made (to this.onOut/this.onErr), for the run whose effects count
    runProlog(text, stream) {
      // a program that changes its clauses keeps one live database for the whole session (as in
      // swipl: what initialization/1 or one goal asserts, the next goal sees)
      if ((this.dynamic || this.prog.dynamic.size) && !this.live) this.live = this.freshProgram();
      const prog = this.live || this.prog;
      const r = P.runQuery(prog, text, { stepLimit: limit(this.stepLimit, this.timeLimitMs), maxAnswers: 1, io: this.io, accel: this.accelFn(), globals: this.globals, onOut: stream ? this.onOut : null, onErr: stream ? this.onErr : null });
      r.error = tidy(r.error); if (stream && (this.onOut || this.onErr)) r.streamed = true; return r;
    }
    runDetlog(plan, native) {
      const was = P.DETLOG_NATIVE; P.DETLOG_NATIVE = native; P.DETLOG_CHECKED = this.checked;
      // a converted route works out every answer before giving one: a goal with endless answers reaches
      // this (smaller) limit there, and Prolog, which stops at the first answer, decides
      try { const r = P.runDetlogFast(plan.detlog, plan.q.pred, plan.q.vars, { stepLimit: limit(Math.min(this.stepLimit, this.convertedSteps || 3e6), Math.min(this.timeLimitMs, 5000)) }); r.error = tidy(r.error); return firstOnly(r); }
      finally { P.DETLOG_NATIVE = was; }
    }
    // the C export, compiled (Node): the answers between \x1e marks, the program's output around them
    runNativeC(plan) {
      if (!this.nativeC) return null;
      if (!plan.cHandle) {
        if (plan.cFailed) return null;
        const code = P.toC(plan.conv.text, { queries: plan.conv.queries, source: plan.conv.source, checked: this.checked, swiWrite: true }).code;
        plan.cHandle = this.nativeC.compile(code);
        if (!plan.cHandle) { plan.cFailed = true; return null; }
      }
      const r = this.nativeC.run(plan.cHandle, ['--events', '--first', '--no-ref']);
      if (!r || r.status !== 0) return { error: (r && r.stderr || 'the C program stopped').trim(), events: [], answers: [], output: '', ms: r && r.ms };
      const a = r.stdout.indexOf('\x1d'), b = r.stdout.lastIndexOf('\x1d');
      if (a < 0 || b <= a) return { error: 'the C program gave no answers', events: [], answers: [], output: '', ms: r.ms };
      const body = r.stdout.slice(a + 1, b), events = [], answers = [];
      const parts = body.split('\x1e');
      parts.forEach((p, i) => { if (i % 2 === 0) { if (p) events.push({ k: 'out', text: p }); } else { const text = p.replace(/\n$/, ''); events.push({ k: 'row', text }); answers.push({ text }); } });
      return { events, answers, output: events.filter((e) => e.k === 'out').map((e) => e.text).join(''), error: null, ms: r.ms };
    }

    // Runs a goal once (as swipl -g does). Returns { status: 'true'|'false'|'error'|'halt', code,
    // output, errOutput, error, route, why, answers, timing }
    run(goalText) {
      const was = P.SWI_WRITE; P.SWI_WRITE = true;
      try { return this._run(goalText); } finally { P.SWI_WRITE = was; }
    }
    _run(goalText) {
      const text = goalText.trim().replace(/\.\s*$/, '');
      const plan = this.plan(text);
      let res, route;
      if (plan.route === 'Prolog' || plan.pick === 'Prolog') { res = this.runProlog(text, true); route = 'Prolog'; }
      else if (plan.pick) {
        res = plan.pick === 'C' ? this.runNativeC(plan) : this.runDetlog(plan, plan.pick === 'C (JS)');
        route = plan.pick;
        if (!res) { res = this.runDetlog(plan, false); route = 'MNN'; }
      } else {
        // first run: one route, the intersection of Detlog MNN and C (the MNN program with its C tier;
        // compiled C on Node when the goal takes a while), checked once against Prolog. On the bundled
        // examples it is the fastest route or within 5% of it, and MNN alone is ~70x slower, so the
        // routes are no longer each timed.
        // (the C tier applies where the compiled program has native modes; it is known after a run)
        const m = time(() => this.runDetlog(plan, true), 0, 1);
        const nat = P.nativeModesOf(plan.detlog).length > 0;
        const limited = /limit/.test(m.r.error || '');
        const pr = limited ? null : time(() => this.runProlog(text), 0, 1);
        const own = nat ? 'C (JS)' : 'MNN';
        const timing = { mnn: nat ? null : m.ms, cjs: nat ? m.ms : null, prolog: pr ? pr.ms : null, c: null };
        const cands = [];
        const agrees = pr && !pr.r.error && !pr.r.halted && !pr.r.errOutput && sameAnswers(firstOnly(pr.r), m.r);
        if (!m.r.error && agrees) cands.push([own, m.ms, m.r]);
        if (this.nativeC && nat && m.ms >= (this.nativeC.minMs || 5) && cands.length) {
          const c = this.runNativeC(plan);
          if (c && !c.error && sameAnswers(c, m.r)) { timing.c = c.ms; cands.push(['C', c.ms, c]); }
          else if (c) plan.notes.push('compiled C: ' + (c.error || 'its answers differ from the MNN route\'s'));
        }
        plan.timing = timing;
        if (!cands.length) { plan.pick = 'Prolog'; plan.why = m.r.error ? 'the converted route raised ' + m.r.error + ': Prolog decides' : 'the routes disagree: Prolog decides'; res = this.runProlog(text, true); route = 'Prolog'; }
        else {
          cands.sort((x, y) => x[1] - y[1]);
          let [name, ms, r] = cands[0];
          plan.pick = name; plan.why = 'the Detlog MNN and C route, its answers checked against Prolog (' + cands.map(([n, t]) => n + ' ' + t.toFixed(3) + ' ms').join(', ') + ')';
          res = r; route = name;
          // Prolog when it is clearly faster (half the time or less). A first run includes compiling,
          // so when Prolog looks faster both are run once more, warm, and those times decide.
          // (cold times are rough, both ways: a first Prolog run also tries its per-call compiling)
          // A goal that takes long is timed well enough by its first runs; a short one is run twice more
          // each way. A goal under PROLOG_MIN_GAIN ms faster stays where it is (timer noise).
          if (pr.ms <= ms * 1.5 && ms - pr.ms >= PROLOG_MIN_GAIN / 2) {
            const best2 = (f) => { const a = time(f, 0, 1), b = time(f, 0, 1); return a.ms <= b.ms ? a : b; };
            const long = ms > 200;
            const warm = name === 'C' || long ? { ms } : best2(() => this.runDetlog(plan, nat));
            const pw = long ? pr : best2(() => this.runProlog(text));
            if (!pw.r.error && sameAnswers(firstOnly(pw.r), r) && pw.ms * PROLOG_FASTER <= warm.ms && warm.ms - pw.ms >= PROLOG_MIN_GAIN) {
              plan.pick = 'Prolog'; route = 'Prolog'; res = pw.r; timing.prolog = pw.ms; timing[name === 'C' ? 'c' : nat ? 'cjs' : 'mnn'] = warm.ms;
              plan.why = 'Prolog, at least ' + PROLOG_FASTER + 'x faster than the Detlog MNN and C route here (' + pw.ms.toFixed(3) + ' ms against ' + name + ' ' + warm.ms.toFixed(3) + ' ms)';
            }
          }
        }
        this.save(plan);
      }
      if (res.error && route !== 'Prolog') {
        // an error on a converted route: Prolog decides
        const pr = this.runProlog(text);
        if (!sameAnswers(firstOnly(pr), res) || pr.error !== res.error) { res = pr; route = 'Prolog'; }
      }
      if (route === 'Prolog') res = Object.assign(firstOnly(res), { errOutput: res.errOutput, halted: res.halted, error: res.error, streamed: res.streamed });
      const status = res.halted != null ? 'halt' : res.error ? 'error' : res.answers.length ? 'true' : 'false';
      return { status, code: res.halted, output: res.output || '', errOutput: res.errOutput || '', error: res.error || null, answers: res.answers.map((a) => a.text), route, why: plan.why, timing: plan.timing, plan, streamed: !!res.streamed };
    }

    // ---- swipl command lines
    // swipl [options] [file ...] [-- arg ...]: -g Goal (repeatable), -t Toplevel, -s File, -l File,
    // -q, -O, --stack-limit=..., file.pl; arguments after -- (or after the script) are the argv flag.
    static parseArgs(args) {
      const spec = { goals: [], toplevel: null, files: [], argv: [], quiet: false };
      let i = 0;
      for (; i < args.length; i++) {
        const a = args[i];
        if (a === '--') { i++; break; }
        if (a === '-g') spec.goals.push(args[++i]);
        else if (a === '-t') spec.toplevel = args[++i];
        else if (a === '-s' || a === '-l' || a === '-f' && args[i + 1] !== 'none') spec.files.push(args[++i]);
        else if (a === '-f') i++;
        else if (a === '-q' || a === '-O' || a === '--quiet' || a === '--traditional' || a === '--no-tty' || /^--(stack[-_]limit|table[-_]space|home|nosignals|no-signals|threads|pce|no-pce)/.test(a)) { if (a === '-q' || a === '--quiet') spec.quiet = true; }
        else if (/^-[a-zA-Z]/.test(a)) { /* other options: ignored */ }
        else { spec.files.push(a); if (/\.(pl|pro|prolog)$/.test(a) && !spec.goals.length) { i++; break; } }
      }
      spec.argv = args.slice(i);
      return spec;
    }
    // Runs a swipl command line. out(s)/err(s) receive the output. Returns the exit code.
    // stream: output is written as the goals make it (else after each goal)
    runArgs(args, { out = () => {}, err = () => {}, stream = false } = {}) {
      const spec = Interpreter.parseArgs(args);
      if (stream) { this.onOut = out; this.onErr = err; }
      this.io.argv = spec.argv;
      const st = this.loadFiles(spec.files);
      for (const f of st.missing) { err('Warning: source_sink `' + f + "' does not exist\n"); }
      if (this.loadError) { err('ERROR: ' + this.loadError + '\n'); }
      const goal = (g, kind) => {
        const r = this.run(g);
        if (this.log) this.log(r);
        if (!r.streamed) { out(r.output); if (r.errOutput) err(r.errOutput); }
        if (r.status === 'halt') return { halt: r.code };
        if (r.status === 'error') { err((kind === 'init' ? 'Warning: ' : 'Warning: ') + 'goal (' + g + ') raised exception:\n' + r.error + '\n'); return { code: 2, failed: true }; }
        if (r.status === 'false') { err('Warning: goal (' + g + ') failed\n'); return { code: 1, failed: true }; }
        return { code: 0 };
      };
      for (const g of st.loadGoals.concat(st.init)) { const r = goal(g, 'init'); if (r.halt != null) return r.halt; }
      if (st.initMain) { const r = goal(st.initMain, 'main'); if (r.halt != null) return r.halt; return r.failed ? 1 : 0; }
      for (const g of spec.goals) { const r = goal(g, 'goal'); if (r.halt != null) return r.halt; if (r.failed) return r.code; }
      if (spec.toplevel && spec.toplevel !== 'halt') { const r = goal(spec.toplevel, 'toplevel'); if (r.halt != null) return r.halt; return r.failed ? 1 : 0; }
      return 0;
    }
  }
  Interpreter.prototype.installTime = function () {
    const B = P.builtins; if (B['time/1'] && B['time/1'].interp) return;
    B['$time_start/1'] = { fn: (a, e) => e.unify(a[0], P.Cmp('t', [P.Num(P.now(), true), P.Int(e.steps)])) };
    B['$time_report/1'] = { fn: (a, e) => { const t = D(a[0]); const ms = P.now() - D(t.a[0]).v, n = e.steps - D(t.a[1]).v; const s = ms / 1000; e.writeErr('% ' + n.toLocaleString('en') + ' inferences, ' + s.toFixed(3) + ' CPU in ' + s.toFixed(3) + ' seconds (100% CPU, ' + (s > 0 ? Math.round(n / s).toLocaleString('en') : 'Infinite') + ' Lips)\n'); return true; } };
    B['time/1'] = { call: true, interp: true, fn: (a) => { const T = P.Var('T'), rep = P.Cmp('$time_report', [T]); return P.Cmp(',', [P.Cmp('$time_start', [T]), P.Cmp(';', [P.Cmp('*->', [P.Cmp('call', [a[0]]), rep]), P.Cmp(',', [rep, P.Atom('fail')])])]); } };
  };

  // Is every use of builtin k that a goal reaches free of effects? format/3 to atom(A), string(S),
  // codes(C) or chars(C) only builds text; current_prolog_flag/2 for a flag other than argv is a constant.
  const SINKS = new Set(['atom', 'string', 'codes', 'chars']);
  function pureUses(prog, goalText, k) {
    if (k !== 'format/3' && k !== 'current_prolog_flag/2') return false;
    let t; try { t = P.readTerm(goalText).term; } catch (e) { return false; }
    const seen = new Set(); let pure = true;
    const visit = (x) => {
      x = D(x); if (!pure) return; const xk = keyOf(x);
      if (xk === k) { const a0 = D(x.a[0]); if (k === 'format/3' ? !(a0.t === 'c' && a0.a.length === 1 && SINKS.has(a0.f)) : !(a0.t === 'a' && a0.n !== 'argv')) { pure = false; return; } }
      if (xk && prog.preds.has(xk) && !seen.has(xk)) { seen.add(xk); for (const cl of prog.preds.get(xk)) visit(cl.body); }
      if (x.t === 'c') x.a.forEach(visit);
    };
    visit(t);
    return pure;
  }

  // the predicates a goal can call that are neither in the program nor built in
  function unknown(prog, goalText) {
    let t; try { t = P.readTerm(goalText).term; } catch (e) { return []; }
    const r = reaches(prog, t), out = [];
    // a program that loads files while it runs defines predicates only then: nothing is known missing
    if (['consult/1', 'use_module/1', 'use_module/2', 'load_files/2', 'ensure_loaded/1'].some((k) => r.has(k))) return [];
    for (const k of r) {
      if (prog.preds.has(k) || P.builtins[k] || P.CONTROL.has(k) || prog.dynamic.has(k)) continue;
      if (/^call\/\d+$/.test(k) || k === ':/2' || /^'?\$/.test(k)) continue;
      // only goals: a key found in data (an atom or a compound used as a value) may not be called at all
      out.push(k);
    }
    return out.filter((k) => calledSomewhere(prog, t, k));
  }
  // is k in goal position somewhere the goal can reach (bodies, and the meta-arguments of control)?
  function calledSomewhere(prog, top, k) {
    const seen = new Set();
    const META = { ',/2': [0, 1], ';/2': [0, 1], '->/2': [0, 1], '*->/2': [0, 1], '\\+/1': [0], 'not/1': [0], 'call/1': [0], 'once/1': [0], 'ignore/1': [0], 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'bagof/3': [1], 'setof/3': [1], 'aggregate_all/3': [1], 'aggregate_all/4': [2], 'catch/3': [0, 2], 'with_output_to/2': [1], 'time/1': [0], '^/2': [1], '$scc/3': [0, 1, 2], 'setup_call_cleanup/3': [0, 1, 2], 'call_cleanup/2': [0, 1] };
    let found = false;
    const goal = (g) => {
      g = D(g); if (found) return; const gk = keyOf(g); if (!gk) return;
      if (gk === k) { found = true; return; }
      if (META[gk]) { for (const i of META[gk]) goal(g.a[i]); return; }
      if (prog.preds.has(gk) && !seen.has(gk)) { seen.add(gk); for (const cl of prog.preds.get(gk)) goal(cl.body); }
    };
    goal(top);
    return found;
  }

  P.Interpreter = Interpreter;
  P.interp = { loadFiles, unknown, reaches, steadfast, pointOne, hash, VERSION, EFFECTS };
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
(function(P){P.C_RUNTIME="/* pl2detlog C runtime for Detlog: terms, unification with a trail, packets, builtins.\n   Generated programs call one C function per Detlog predicate; there are no choicepoints:\n   each call commits to the clause its first argument selects, and if_commit/3 is compiled to\n   \"mark the trail, run the condition, undo and take the else branch if it failed\". BSD-3-Clause. */\n#include <stdio.h>\n#include <stddef.h>\n#include <stdlib.h>\n#include <string.h>\n#include <math.h>\n#include <stdint.h>\n#include <time.h>\n#include <ctype.h>\n\nenum { T_VAR, T_ATOM, T_INT, T_FLT, T_STR, T_CMP };\ntypedef struct Term Term;\n/* 40 bytes: the fields a term of each kind uses share their space (a variable: ref, cp, id; an atom,\n   string or compound: name, args; a number: iv or fv). cpe is the copy epoch of a variable and the\n   ground mark of a compound. A compound's arguments follow it in the same allocation. */\nstruct Term {\n  int tag; int arity; long cpe;\n  union {\n    struct { const char *name; Term **args; };\n    struct { Term *ref; Term *cp; };\n    long long iv;\n    double fv;\n  };\n  long id;\n};\nstatic long dl_steps = 0, dl_step_limit = 200000000L, dl_decisions = 0, dl_var_id = 0, dl_memo_hits = 0;\nstatic void dl_die(const char *m, const char *x) { fprintf(stderr, \"Detlog runtime error: %s%s%s\\n\", m, x ? \" \" : \"\", x ? x : \"\"); exit(2); }\n#ifdef DL_CHECKED\n#define STEP() do { if (++dl_steps > dl_step_limit) dl_die(\"step limit exceeded\", NULL); } while (0)\n#else\n#define STEP() ((void)0) /* unchecked (the default): no step limit, no step count */\n#endif\n\n/* ---------- memory ---------- */\nstatic char *arena = NULL; static size_t arena_left = 0;\n/* chunks, so that a run can be undone: arena_mark() before it, arena_release() after (repeated timing runs) */\nstatic char **chunks = NULL; static size_t *chunk_size = NULL; static size_t nchunks = 0, chunk_cap = 0;\nstatic char *spare[64]; static size_t spare_size[64]; static size_t nspare = 0; /* chunks of released runs */\nstatic char *parena = NULL; static size_t pleft = 0; static int pinned = 0; /* kept for the whole run (built tables) */\nstatic void *alloc_slow(size_t n) {\n  if (pinned) { if (n > pleft) { size_t sz = n > (1u << 20) ? n : (1u << 20); parena = (char *)malloc(sz); if (!parena) dl_die(\"out of memory\", NULL); pleft = sz; } void *p = parena; parena += n; pleft -= n; return p; }\n  if (n > arena_left) {\n    /* a chunk kept from a released run is used again (its pages are already mapped) */\n    if (nspare && n <= spare_size[nspare - 1]) { nspare--; arena = spare[nspare]; arena_left = spare_size[nspare];\n      if (nchunks == chunk_cap) { chunk_cap = chunk_cap ? chunk_cap * 2 : 16; chunks = (char **)realloc(chunks, chunk_cap * sizeof(char *)); chunk_size = (size_t *)realloc(chunk_size, chunk_cap * sizeof(size_t)); }\n      chunks[nchunks] = arena; chunk_size[nchunks] = arena_left; nchunks++;\n      void *p = arena; arena += n; arena_left -= n; return p; }\n    size_t sz = n > (1u << 22) ? n : (1u << 22); arena = (char *)malloc(sz); if (!arena) dl_die(\"out of memory\", NULL); arena_left = sz;\n    if (nchunks == chunk_cap) { chunk_cap = chunk_cap ? chunk_cap * 2 : 16; chunks = (char **)realloc(chunks, chunk_cap * sizeof(char *)); chunk_size = (size_t *)realloc(chunk_size, chunk_cap * sizeof(size_t)); }\n    chunks[nchunks] = arena; chunk_size[nchunks] = sz; nchunks++;\n  }\n  void *p = arena; arena += n; arena_left -= n; return p;\n}\n/* 8-byte aligned bump allocation; the slow path takes a new chunk (or the pinned arena) */\nstatic inline void *alloc(size_t n) {\n  n = (n + 7) & ~(size_t)7;\n  if (n <= arena_left && !pinned) { void *p = arena; arena += n; arena_left -= n; return p; }\n  return alloc_slow(n);\n}\ntypedef struct { size_t nchunks; char *arena; size_t left; } ArenaMark;\nstatic ArenaMark arena_mark(void) { ArenaMark m = { nchunks, arena, arena_left }; return m; }\nstatic void arena_release(ArenaMark m) {\n  while (nchunks > m.nchunks) { nchunks--; if (nspare < 64) { spare[nspare] = chunks[nchunks]; spare_size[nspare++] = chunk_size[nchunks]; } else free(chunks[nchunks]); }\n  arena = m.arena; arena_left = m.left;\n}\nstatic Term *new_term(int tag) { Term *t = (Term *)alloc(sizeof(Term)); memset(t, 0, sizeof(Term)); t->tag = tag; return t; }\n\n/* ---------- atoms ---------- */\n#define AH 8192\nstatic Term *atab[AH];\nstatic unsigned long hstr(const char *s) { unsigned long h = 5381; while (*s) h = h * 33 + (unsigned char)*s++; return h; }\nstatic Term *mk_atom(const char *s) {\n  unsigned long h = hstr(s) % AH;\n  for (;;) { Term *t = atab[h]; if (!t) break; if (strcmp(t->name, s) == 0) return t; h = (h + 1) % AH; }\n  /* atoms are interned for the whole program: outside the arena, which a timing run may release */\n  Term *t = (Term *)calloc(1, sizeof(Term)); char *c = (char *)malloc(strlen(s) + 1); if (!t || !c) dl_die(\"out of memory\", NULL);\n  t->tag = T_ATOM; strcpy(c, s); t->name = c; atab[h] = t; return t;\n}\nstatic const char *intern(const char *s) { return mk_atom(s)->name; }\nstatic Term *NIL, *A_TRUE, *A_E, *A_OUT, *A_FOUND, *A_NONE, *A_MINUS, *A_DOT;\n/* small integers are shared: integers are never changed, so one term serves every use */\n#define ICACHE_LO (-1024)\n#define ICACHE_HI 65535\nstatic Term icache[ICACHE_HI - ICACHE_LO + 1];\nstatic Term *mk_int(long long v) {\n  if (v >= ICACHE_LO && v <= ICACHE_HI) { Term *t = &icache[v - ICACHE_LO]; if (!t->tag) { t->tag = T_INT; t->iv = v; } return t; }\n  Term *t = new_term(T_INT); t->iv = v; return t;\n}\nstatic Term *mk_flt(double v) { Term *t = new_term(T_FLT); t->fv = v; return t; }\nstatic Term *mk_str(const char *s) { Term *t = new_term(T_STR); char *c = (char *)alloc(strlen(s) + 1); strcpy(c, s); t->name = c; return t; }\nstatic Term *mk_var(void) { Term *t = new_term(T_VAR); t->id = ++dl_var_id; return t; }\n#define GR_MARK (-1L)\n#define GND(x) ((x)->tag != T_VAR && ((x)->tag != T_CMP || (x)->cpe == GR_MARK))\n/* a compound and its arguments are one allocation */\nstatic Term *mk_cmp(const char *f, int n, Term **a) {\n  if (n == 0) return mk_atom(f);\n  Term *t = (Term *)alloc(sizeof(Term) + sizeof(Term *) * n); memset(t, 0, sizeof(Term));\n  t->tag = T_CMP; t->name = f; t->arity = n; t->args = (Term **)(t + 1);\n  memcpy(t->args, a, sizeof(Term *) * n);\n  int g = 1; for (int i = 0; i < n && g; i++) g = GND(a[i]); if (g) t->cpe = GR_MARK;\n  return t;\n}\nstatic inline Term *mk_cons(Term *h, Term *tl) {\n  Term *t = (Term *)alloc(offsetof(Term, id) + 2 * sizeof(Term *)); /* the two arguments take id's place and the 8 bytes after it: 48 bytes a cell */\n  t->tag = T_CMP; t->arity = 2; t->name = A_DOT->name; t->args = (Term **)&t->id; t->args[0] = h; t->args[1] = tl;\n  /* a cell over ground parts is ground (no variable can later appear in it): marked now, so copying and\n     resolving it later stop here instead of walking the list */\n  t->cpe = (GND(h) && GND(tl)) ? GR_MARK : 0;\n  return t;\n}\nstatic Term *deref(Term *t) { while (t->tag == T_VAR && t->ref) t = t->ref; return t; }\n/* a cell the native tier builds: its parts are ground by the native contract (ground inputs), so it is marked\n   without looking at them */\nstatic inline Term *mk_gcons(Term *h, Term *tl) {\n  Term *t = (Term *)alloc(offsetof(Term, id) + 2 * sizeof(Term *)); /* the two arguments take id's place and the 8 bytes after it: 48 bytes a cell */\n  t->tag = T_CMP; t->arity = 2; t->name = A_DOT->name; t->args = (Term **)&t->id; t->args[0] = h; t->args[1] = tl; t->cpe = GR_MARK;\n  return t;\n}\nstatic int is_cons(Term *t) { return t->tag == T_CMP && t->arity == 2 && t->name == A_DOT->name; }\nstatic int is_nil(Term *t) { return t == NIL; }\n\n/* ---------- growable arrays ---------- */\ntypedef struct { Term **v; size_t n, cap; } TV;\n/* term vectors' buffers are reused: a freed buffer goes on a free list by size (a power of two), so a vector\n   that is made and freed on every call costs no malloc after the first */\nstatic Term **tvb_free[32];\nstatic Term **tvb_get(size_t cap, unsigned cls) {\n  Term **b = tvb_free[cls];\n  if (b) { tvb_free[cls] = (Term **)b[-1]; b[-1] = (Term *)(size_t)cls; return b; }\n  b = (Term **)malloc(sizeof(Term *) * (cap + 1)); if (!b) dl_die(\"out of memory\", NULL);\n  b[0] = (Term *)(size_t)cls; return b + 1;\n}\nstatic void tv_free(Term **b) { if (!b) return; unsigned cls = (unsigned)(size_t)b[-1]; b[-1] = (Term *)tvb_free[cls]; tvb_free[cls] = b; }\nstatic void tv_grow(TV *a) { size_t cap = a->cap ? a->cap * 2 : 16; unsigned cls = 0; while (((size_t)16 << cls) < cap) cls++; Term **nb = tvb_get(cap, cls); if (a->n) memcpy(nb, a->v, sizeof(Term *) * a->n); tv_free(a->v); a->v = nb; a->cap = cap; }\nstatic inline void tv_push(TV *a, Term *x) { if (a->n == a->cap) tv_grow(a); a->v[a->n++] = x; }\nstatic Term *tv_list(TV *a) { Term *r = NIL; for (size_t i = a->n; i-- > 0;) r = mk_cons(a->v[i], r); return r; }\nstatic int list_to_tv(Term *t, TV *out) { t = deref(t); while (is_cons(t)) { tv_push(out, t->args[0]); t = deref(t->args[1]); } return is_nil(t); }\n\n/* ---------- trail ---------- */\nstatic TV trail;\n#define TR_TOP (trail.n)\nstatic void bind(Term *v, Term *t) { v->ref = t; tv_push(&trail, v); }\nstatic void undo(size_t m) { while (trail.n > m) trail.v[--trail.n]->ref = NULL; }\n\n/* ---------- unify / compare / copy ---------- */\n/* unify: the pairs still to do are kept on a small stack in the frame, moved to the heap only for big terms */\nstatic int unify(Term *a, Term *b) {\n  a = deref(a); b = deref(b);\n  if (a == b) return 1;\n  if (a->tag == T_VAR) { bind(a, b); return 1; }\n  if (b->tag == T_VAR) { bind(b, a); return 1; }\n  if (a->tag != T_CMP || b->tag != T_CMP) {\n    if (a->tag != b->tag) return 0;\n    switch (a->tag) { case T_INT: return a->iv == b->iv; case T_FLT: return a->fv == b->fv; case T_STR: return !strcmp(a->name, b->name); default: return 0; }\n  }\n  Term *loc[64]; Term **sv = loc; size_t n = 0, cap = 64; int ok = 1;\n  sv[n++] = a; sv[n++] = b;\n  while (n) {\n    Term *y = deref(sv[--n]), *x = deref(sv[--n]);\n    if (x == y) continue;\n    if (x->tag == T_VAR) { bind(x, y); continue; }\n    if (y->tag == T_VAR) { bind(y, x); continue; }\n    if (x->tag != y->tag) { ok = 0; break; }\n    if (x->tag == T_ATOM) { ok = 0; break; }\n    if (x->tag == T_INT) { if (x->iv != y->iv) { ok = 0; break; } continue; }\n    if (x->tag == T_FLT) { if (x->fv != y->fv) { ok = 0; break; } continue; }\n    if (x->tag == T_STR) { if (strcmp(x->name, y->name)) { ok = 0; break; } continue; }\n    if (x->name != y->name || x->arity != y->arity) { ok = 0; break; }\n    if (n + 2 * (size_t)x->arity > cap) {\n      size_t nc = cap; while (n + 2 * (size_t)x->arity > nc) nc *= 2;\n      Term **nv = (Term **)malloc(sizeof(Term *) * nc); if (!nv) dl_die(\"out of memory\", NULL);\n      memcpy(nv, sv, sizeof(Term *) * n); if (sv != loc) free(sv); sv = nv; cap = nc;\n    }\n    for (int i = x->arity; i-- > 0;) { sv[n++] = x->args[i]; sv[n++] = y->args[i]; }\n  }\n  if (sv != loc) free(sv); return ok;\n}\nstatic int rank(Term *t) { switch (t->tag) { case T_VAR: return 0; case T_INT: case T_FLT: return 1; case T_ATOM: return 3; case T_STR: return 4; default: return 5; } }\nstatic int compare(Term *a, Term *b) {\n  a = deref(a); b = deref(b); if (a == b) return 0;\n  int ra = rank(a), rb = rank(b); if (ra != rb) return ra < rb ? -1 : 1;\n  switch (a->tag) {\n    case T_VAR: return a->id < b->id ? -1 : 1;\n    case T_INT: case T_FLT: {\n      double x = a->tag == T_INT ? (double)a->iv : a->fv, y = b->tag == T_INT ? (double)b->iv : b->fv;\n      if (x != y) return x < y ? -1 : 1; if (a->tag != b->tag) return a->tag == T_FLT ? -1 : 1; return 0; }\n    case T_ATOM: case T_STR: { int c = strcmp(a->name, b->name); return c < 0 ? -1 : c > 0; }\n    default:\n      if (a->arity != b->arity) return a->arity < b->arity ? -1 : 1;\n      { int c = strcmp(a->name, b->name); if (c) return c < 0 ? -1 : 1; }\n      for (int i = 0; i < a->arity; i++) { int c = compare(a->args[i], b->args[i]); if (c) return c; }\n      return 0;\n  }\n}\nstatic long copy_epoch = 0;\n/* A compound whose arguments a copy found identical (no variable cell anywhere, bound or not) is marked ground\n   in its cpe field, which compounds do not otherwise use: no undo can change it, so copies share it. */\nstatic Term *copy_rec(Term *t) {\n  t = deref(t);\n  if (t->tag == T_VAR) { if (t->cpe != copy_epoch) { t->cpe = copy_epoch; t->cp = mk_var(); } return t->cp; }\n  if (t->tag != T_CMP || t->cpe == GR_MARK) return t;\n  if (is_cons(t)) {\n    TV hs = { 0 }, cs = { 0 }; Term *x = t;\n    while (is_cons(x) && x->cpe != GR_MARK) { tv_push(&cs, x); tv_push(&hs, copy_rec(x->args[0])); x = deref(x->args[1]); }\n    Term *r = copy_rec(x);\n    for (size_t i = hs.n; i-- > 0;) { Term *c = cs.v[i]; if (hs.v[i] == c->args[0] && r == c->args[1]) { c->cpe = GR_MARK; r = c; } else r = mk_cons(hs.v[i], r); }\n    tv_free(hs.v); tv_free(cs.v); return r;\n  }\n  Term **a = (Term **)alloc(sizeof(Term *) * t->arity); int same = 1;\n  for (int i = 0; i < t->arity; i++) { a[i] = copy_rec(t->args[i]); if (a[i] != t->args[i]) same = 0; }\n  if (same) { t->cpe = GR_MARK; return t; }\n  Term *r = new_term(T_CMP); r->name = t->name; r->arity = t->arity; r->args = a; return r;\n}\nstatic Term *copy_term(Term *t) { copy_epoch++; return copy_rec(t); }\nstatic Term *resolve(Term *t) {\n  t = deref(t);\n  if (t->tag != T_CMP || t->cpe == GR_MARK) return t;\n  if (is_cons(t)) {\n    TV hs = { 0 }, cs = { 0 }; Term *x = t;\n    while (is_cons(x) && x->cpe != GR_MARK) { tv_push(&cs, x); tv_push(&hs, resolve(x->args[0])); x = deref(x->args[1]); }\n    Term *r = resolve(x);\n    /* resolve keeps unbound variables, so a cell is shared (and marked ground) only with no variable below */\n    for (size_t i = hs.n; i-- > 0;) {\n      Term *c = cs.v[i], *h = hs.v[i];\n      int g = h->tag != T_VAR && (h->tag != T_CMP || h->cpe == GR_MARK) && r->tag != T_VAR && (r->tag != T_CMP || r->cpe == GR_MARK);\n      if (h == c->args[0] && r == c->args[1] && g) { c->cpe = GR_MARK; r = c; } else r = mk_cons(h, r);\n    }\n    tv_free(hs.v); tv_free(cs.v); return r;\n  }\n  Term **a = (Term **)alloc(sizeof(Term *) * t->arity); int same = 1, g = 1;\n  for (int i = 0; i < t->arity; i++) { a[i] = resolve(t->args[i]); if (a[i] != t->args[i]) same = 0; if (a[i]->tag == T_VAR || (a[i]->tag == T_CMP && a[i]->cpe != GR_MARK)) g = 0; }\n  if (same && g) { t->cpe = GR_MARK; return t; }\n  Term *r = new_term(T_CMP); r->name = t->name; r->arity = t->arity; r->args = a; return r;\n}\nstatic int is_ground(Term *t) { t = deref(t); if (t->tag == T_VAR) return 0; if (t->tag == T_CMP) { if (t->cpe == GR_MARK) return 1; for (int i = 0; i < t->arity; i++) if (!is_ground(t->args[i])) return 0; } return 1; }\nstatic void term_vars(Term *t, TV *out) {\n  t = deref(t);\n  if (t->tag == T_VAR) { for (size_t i = 0; i < out->n; i++) if (out->v[i] == t) return; tv_push(out, t); return; }\n  if (t->tag == T_CMP) for (int i = 0; i < t->arity; i++) term_vars(t->args[i], out);\n}\n\n/* ---------- strings ---------- */\ntypedef struct { char *s; size_t n, cap; } SB;\nstatic void sb_putn(SB *b, const char *s, size_t n) { if (b->n + n + 1 > b->cap) { b->cap = (b->n + n + 1) * 2; b->s = (char *)realloc(b->s, b->cap); } memcpy(b->s + b->n, s, n); b->n += n; b->s[b->n] = 0; }\nstatic void sb_puts(SB *b, const char *s) { sb_putn(b, s, strlen(s)); }\nstatic void sb_putc(SB *b, char c) { sb_putn(b, &c, 1); }\n\n/* ---------- printing (matches pl2detlog's JS printer) ---------- */\ntypedef struct { const char *n; int p; const char *type; } Op;\nstatic const Op infix_ops[] = {\n  {\":-\",1200,\"xfx\"},{\"-->\",1200,\"xfx\"},{\";\",1100,\"xfy\"},{\"|\",1100,\"xfy\"},{\"->\",1050,\"xfy\"},{\"*->\",1050,\"xfy\"},{\",\",1000,\"xfy\"},{\":=\",990,\"xfx\"},\n  {\"=\",700,\"xfx\"},{\"\\\\=\",700,\"xfx\"},{\"==\",700,\"xfx\"},{\"\\\\==\",700,\"xfx\"},{\"@<\",700,\"xfx\"},{\"@>\",700,\"xfx\"},{\"@=<\",700,\"xfx\"},{\"@>=\",700,\"xfx\"},\n  {\"=..\",700,\"xfx\"},{\"is\",700,\"xfx\"},{\"=:=\",700,\"xfx\"},{\"=\\\\=\",700,\"xfx\"},{\"<\",700,\"xfx\"},{\">\",700,\"xfx\"},{\"=<\",700,\"xfx\"},{\">=\",700,\"xfx\"},\n  {\">:<\",700,\"xfx\"},{\":<\",700,\"xfx\"},{\"as\",700,\"xfx\"},{\":\",200,\"xfy\"},{\"+\",500,\"yfx\"},{\"-\",500,\"yfx\"},{\"/\\\\\",500,\"yfx\"},{\"\\\\/\",500,\"yfx\"},{\"xor\",500,\"yfx\"},\n  {\"*\",400,\"yfx\"},{\"/\",400,\"yfx\"},{\"//\",400,\"yfx\"},{\"rem\",400,\"yfx\"},{\"mod\",400,\"yfx\"},{\"div\",400,\"yfx\"},{\"<<\",400,\"yfx\"},{\">>\",400,\"yfx\"},\n  {\"divmod\",400,\"yfx\"},{\"rdiv\",400,\"yfx\"},{\"**\",200,\"xfx\"},{\"^\",200,\"xfy\"},{\".\",100,\"yfx\"},{NULL,0,NULL} };\nstatic const Op prefix_ops[] = { {\":-\",1200,\"fx\"},{\"?-\",1200,\"fx\"},{\"\\\\+\",900,\"fy\"},{\"?\",500,\"fx\"},{\"-\",200,\"fy\"},{\"+\",200,\"fy\"},{\"\\\\\",200,\"fy\"},{\"$\",1,\"fx\"},\n  {\"dynamic\",1150,\"fx\"},{\"discontiguous\",1150,\"fx\"},{\"initialization\",1150,\"fx\"},{\"table\",1150,\"fx\"},{NULL,0,NULL} };\nstatic const Op *find_op(const Op *t, const char *n) { for (; t->n; t++) if (!strcmp(t->n, n)) return t; return NULL; }\nstatic int is_symch(char c) { return c && strchr(\"+-*/\\\\^<>=~:.?@#&$\", c) != NULL; }\nstatic int atom_needs_quote(const char *n) {\n  if (!strcmp(n, \"[]\") || !strcmp(n, \"!\") || !strcmp(n, \";\") || !strcmp(n, \"{}\")) return 0;\n  if (!strcmp(n, \",\")) return 1;\n  if (*n >= 'a' && *n <= 'z') { for (const char *p = n; *p; p++) if (!(*p == '_' || (*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9'))) return 1; return 0; }\n  if (*n) { for (const char *p = n; *p; p++) if (!is_symch(*p)) return 1; return 0; }\n  return 1;\n}\nstatic void put_atom(SB *b, const char *n, int q) {\n  if (!q || !atom_needs_quote(n)) { sb_puts(b, n); return; }\n  sb_putc(b, '\\'');\n  for (const char *p = n; *p; p++) { if (*p == '\\\\') sb_puts(b, \"\\\\\\\\\"); else if (*p == '\\'') sb_puts(b, \"\\\\'\"); else if (*p == '\\n') sb_puts(b, \"\\\\n\"); else if (*p == '\\t') sb_puts(b, \"\\\\t\"); else sb_putc(b, *p); }\n  sb_putc(b, '\\'');\n}\nstatic void put_float(SB *b, double v) {\n  char buf[64];\n  if (isinf(v)) { sb_puts(b, v > 0 ? \"inf\" : \"-inf\"); return; }\n  if (isnan(v)) { sb_puts(b, \"nan\"); return; }\n  for (int p = 1; p <= 17; p++) { snprintf(buf, sizeof buf, \"%.*g\", p, v); if (strtod(buf, NULL) == v) break; }\n  /* JS style exponent: 1e-7, 1e+21 */\n  char *e = strchr(buf, 'e');\n  if (e) { char mant[64], ex[16]; size_t ml = (size_t)(e - buf); memcpy(mant, buf, ml); mant[ml] = 0; int x = atoi(e + 1);\n    if (x >= -6 && x < 21) { snprintf(buf, sizeof buf, \"%.17g\", v); /* fall back */ char tmp[64]; for (int p = 1; p <= 17; p++) { snprintf(tmp, sizeof tmp, \"%.*f\", p, v); if (strtod(tmp, NULL) == v) { strcpy(buf, tmp); break; } } }\n    else { snprintf(ex, sizeof ex, \"e%c%d\", x < 0 ? '-' : '+', x < 0 ? -x : x); snprintf(buf, sizeof buf, \"%s%s\", mant, ex); } }\n  sb_puts(b, buf);\n  if (!strchr(buf, '.') && !strchr(buf, 'e') && !strchr(buf, 'n') && !strchr(buf, 'i')) sb_puts(b, \".0\");\n}\nstatic void put_str_json(SB *b, const char *s) {\n  sb_putc(b, '\"');\n  for (const unsigned char *p = (const unsigned char *)s; *p; p++) {\n    if (*p == '\"') sb_puts(b, \"\\\\\\\"\"); else if (*p == '\\\\') sb_puts(b, \"\\\\\\\\\"); else if (*p == '\\n') sb_puts(b, \"\\\\n\"); else if (*p == '\\t') sb_puts(b, \"\\\\t\"); else if (*p == '\\r') sb_puts(b, \"\\\\r\");\n    else if (*p < 0x20) { char u[8]; snprintf(u, sizeof u, \"\\\\u%04x\", *p); sb_puts(b, u); } else sb_putc(b, (char)*p);\n  }\n  sb_putc(b, '\"');\n}\nstatic TV show_vars;\nstatic void show(SB *b, Term *t, int q, int maxp);\n/* write/print/format lay terms out as SWI-Prolog writes them when compiled with -DDL_SWI_WRITE (the\n   interpreter): no space after commas, none around symbolic operators. Answers keep the toplevel's. */\nstatic int swi_lay = 0;\n#ifdef DL_SWI_WRITE\n#define SWIQ 1\n#else\n#define SWIQ 0\n#endif\n#define SEP (swi_lay ? \",\" : \", \")\nstatic void show_str(SB *b, Term *t, int q, int maxp) { show(b, t, q, maxp); }\nstatic void show(SB *b, Term *t, int q, int maxp) {\n  t = deref(t);\n  char buf[64];\n  switch (t->tag) {\n    case T_VAR: { size_t i; for (i = 0; i < show_vars.n; i++) if (show_vars.v[i] == t) break; if (i == show_vars.n) tv_push(&show_vars, t);\n      /* _A, _B, ... _Z, _AA ... as the JS printer names them */\n      char nb[16]; int k = (int)i, l = 0; char tmp[16]; do { tmp[l++] = (char)('A' + k % 26); k = k / 26 - 1; } while (k >= 0);\n      nb[0] = '_'; for (int j = 0; j < l; j++) nb[1 + j] = tmp[l - 1 - j]; nb[1 + l] = 0; sb_puts(b, nb); return; }\n    case T_INT: snprintf(buf, sizeof buf, \"%lld\", t->iv); sb_puts(b, buf); return;\n    case T_FLT: put_float(b, t->fv); return;\n    case T_STR: if (q) put_str_json(b, t->name); else sb_puts(b, t->name); return;\n    case T_ATOM: {\n      const Op *io = find_op(infix_ops, t->name), *po = find_op(prefix_ops, t->name);\n      int special = !strcmp(t->name, \"[]\") || !strcmp(t->name, \"{}\") || !strcmp(t->name, \"!\") || !strcmp(t->name, \";\");\n      if ((io || po) && maxp < 1200 && !special) { int p = io ? io->p : 0; if (po && po->p > p) p = po->p; if (p > maxp) { sb_putc(b, '('); put_atom(b, t->name, q); sb_putc(b, ')'); return; } }\n      put_atom(b, t->name, q); return; }\n    case T_CMP: break;\n  }\n  if (is_cons(t)) {\n    sb_putc(b, '['); Term *x = t; int first = 1;\n    while (is_cons(x)) { if (!first) sb_puts(b, SEP); first = 0; show(b, x->args[0], q, 999); x = deref(x->args[1]); }\n    if (!is_nil(x)) { sb_putc(b, '|'); show(b, x, q, 999); }\n    sb_putc(b, ']'); return;\n  }\n  if (!strcmp(t->name, \"{}\") && t->arity == 1) { sb_putc(b, '{'); show(b, t->args[0], q, 1200); sb_putc(b, '}'); return; }\n  if (t->arity == 2) {\n    const Op *op = find_op(infix_ops, t->name);\n    if (op) {\n      int p = op->p, lp = op->type[0] == 'y' ? p : p - 1, rp = op->type[2] == 'y' ? p : p - 1;\n      SB l = { 0 }, r = { 0 }; show(&l, t->args[0], q, lp); show(&r, t->args[1], q, rp);\n      if (!l.s) sb_puts(&l, \"\"); if (!r.s) sb_puts(&r, \"\");\n      if (p > maxp) sb_putc(b, '(');\n      if (!strcmp(t->name, \",\")) { sb_puts(b, l.s); sb_puts(b, SEP); sb_puts(b, r.s); }\n      else {\n        const char *n = t->name;\n        int spaced = (*n >= 'a' && *n <= 'z') || !swi_lay && (p >= 700 || !strcmp(n, \"->\") || !strcmp(n, \":-\") || !strcmp(n, \"-->\") || !strcmp(n, \";\") || !strcmp(n, \"*->\"));\n        if (spaced) { sb_puts(b, l.s); sb_putc(b, ' '); put_atom(b, n, q); sb_putc(b, ' '); sb_puts(b, r.s); }\n        else {\n          SB ft = { 0 }; put_atom(&ft, n, q);\n          int glueR = is_symch(ft.s[ft.n - 1]) && (is_symch(r.s[0]) || (r.s[0] == '-' && r.s[1] >= '0' && r.s[1] <= '9'));\n          int glueL = is_symch(ft.s[0]) && l.n && is_symch(l.s[l.n - 1]);\n          sb_puts(b, l.s); if (glueL) sb_putc(b, ' '); sb_puts(b, ft.s); if (glueR) sb_putc(b, ' '); sb_puts(b, r.s); free(ft.s);\n        }\n      }\n      if (p > maxp) sb_putc(b, ')');\n      free(l.s); free(r.s); return;\n    }\n  }\n  if (t->arity == 1) {\n    const Op *op = find_op(prefix_ops, t->name);\n    if (op) {\n      int p = op->p, ap = !strcmp(op->type, \"fy\") ? p : p - 1;\n      Term *a0 = deref(t->args[0]);\n      SB as = { 0 }; show(&as, a0, q, ap); if (!as.s) sb_puts(&as, \"\");\n      SB ft = { 0 }; put_atom(&ft, t->name, q);\n      int need = (ft.s[0] >= 'a' && ft.s[0] <= 'z') || (ft.s[0] >= 'A' && ft.s[0] <= 'Z') || !swi_lay && !strcmp(ft.s, \"\\\\+\") || (is_symch(ft.s[ft.n - 1]) && (is_symch(as.s[0]) || a0->tag == T_INT || a0->tag == T_FLT)) || as.s[0] == '(';\n      if (p > maxp) sb_putc(b, '(');\n      sb_puts(b, ft.s); if (need) sb_putc(b, ' '); sb_puts(b, as.s);\n      if (p > maxp) sb_putc(b, ')');\n      free(as.s); free(ft.s); return;\n    }\n  }\n  put_atom(b, t->name, q); sb_putc(b, '(');\n  for (int i = 0; i < t->arity; i++) { if (i) sb_puts(b, SEP); show(b, t->args[i], q, 999); }\n  sb_putc(b, ')');\n}\nstatic char *show_term(Term *t, int q) { SB b = { 0 }; show(&b, t, q, 1200); if (!b.s) sb_puts(&b, \"\"); return b.s; }\n#ifdef DL_SWI_WRITE\nstatic char *show_w(Term *t, int q) { swi_lay = 1; char *s = show_term(t, q); swi_lay = 0; return s; }\n#else\n#define show_w show_term\n#endif\n/* text of an atom, string, number or code/char list */\nstatic char *text_of(Term *t) {\n  t = deref(t); SB b = { 0 }; sb_puts(&b, \"\");\n  if (t->tag == T_ATOM || t->tag == T_STR) { sb_puts(&b, t->name); return b.s; }\n  if (t->tag == T_INT || t->tag == T_FLT) { free(b.s); return show_term(t, 0); }\n  TV xs = { 0 };\n  if (list_to_tv(t, &xs)) { for (size_t i = 0; i < xs.n; i++) { Term *x = deref(xs.v[i]); if (x->tag == T_INT) { char c[8]; long long cp = x->iv; if (cp < 0x80) { c[0] = (char)cp; c[1] = 0; } else if (cp < 0x800) { c[0] = (char)(0xC0 | (cp >> 6)); c[1] = (char)(0x80 | (cp & 63)); c[2] = 0; } else { c[0] = (char)(0xE0 | (cp >> 12)); c[1] = (char)(0x80 | ((cp >> 6) & 63)); c[2] = (char)(0x80 | (cp & 63)); c[3] = 0; } sb_puts(&b, c); } else if (x->tag == T_ATOM) sb_puts(&b, x->name); else dl_die(\"text expected\", NULL); } tv_free(xs.v); return b.s; }\n  dl_die(\"text expected\", show_term(t, 1)); return NULL;\n}\n\n/* ---------- arithmetic ---------- */\ntypedef struct { int f; long long i; double d; } Num;\nstatic double nd(Num x) { return x.f ? x.d : (double)x.i; }\nstatic Num NI(long long v) { Num n = { 0, v, 0 }; return n; }\nstatic Num NF(double v) { Num n = { 1, 0, v }; return n; }\nstatic Num eval(Term *t);\nstatic Num eval(Term *t) {\n  t = deref(t);\n  switch (t->tag) {\n    case T_INT: return NI(t->iv);\n    case T_FLT: return NF(t->fv);\n    case T_VAR: dl_die(\"instantiation error in arithmetic\", NULL);\n    case T_ATOM:\n      if (!strcmp(t->name, \"pi\")) return NF(M_PI); if (!strcmp(t->name, \"e\")) return NF(M_E);\n      if (!strcmp(t->name, \"inf\") || !strcmp(t->name, \"infinite\")) return NF(INFINITY); if (!strcmp(t->name, \"nan\")) return NF(NAN);\n      if (!strcmp(t->name, \"max_tagged_integer\")) return NI(9007199254740991LL);\n      if (!strcmp(t->name, \"random\")) return NF((double)rand() / RAND_MAX);\n      dl_die(\"not evaluable:\", t->name);\n    case T_STR: if (strlen(t->name) == 1) return NI((unsigned char)t->name[0]); dl_die(\"not evaluable string\", t->name);\n  }\n  const char *f = t->name;\n  if (is_cons(t) && is_nil(deref(t->args[1]))) return eval(t->args[0]);\n  if (t->arity == 1) {\n    Num a = eval(t->args[0]);\n    if (!strcmp(f, \"-\")) return a.f ? NF(-a.d) : NI(-a.i);\n    if (!strcmp(f, \"+\")) return a;\n    if (!strcmp(f, \"abs\")) return a.f ? NF(fabs(a.d)) : NI(a.i < 0 ? -a.i : a.i);\n    if (!strcmp(f, \"sign\")) return a.f ? NF(a.d > 0 ? 1 : a.d < 0 ? -1 : 0) : NI(a.i > 0 ? 1 : a.i < 0 ? -1 : 0);\n    if (!strcmp(f, \"sqrt\")) return NF(sqrt(nd(a)));\n    if (!strcmp(f, \"sin\")) return NF(sin(nd(a))); if (!strcmp(f, \"cos\")) return NF(cos(nd(a))); if (!strcmp(f, \"tan\")) return NF(tan(nd(a)));\n    if (!strcmp(f, \"asin\")) return NF(asin(nd(a))); if (!strcmp(f, \"acos\")) return NF(acos(nd(a))); if (!strcmp(f, \"atan\")) return NF(atan(nd(a)));\n    if (!strcmp(f, \"exp\")) return NF(exp(nd(a))); if (!strcmp(f, \"log\")) return NF(log(nd(a))); if (!strcmp(f, \"log2\")) return NF(log2(nd(a)));\n    if (!strcmp(f, \"float\")) return NF(nd(a)); if (!strcmp(f, \"integer\")) return NI((long long)llround(nd(a)));\n    if (!strcmp(f, \"truncate\")) return NI((long long)trunc(nd(a))); if (!strcmp(f, \"round\")) return NI((long long)llround(nd(a)));\n    if (!strcmp(f, \"ceiling\")) return NI((long long)ceil(nd(a))); if (!strcmp(f, \"floor\")) return NI((long long)floor(nd(a)));\n    if (!strcmp(f, \"float_integer_part\")) return NF(trunc(nd(a))); if (!strcmp(f, \"float_fractional_part\")) return NF(nd(a) - trunc(nd(a)));\n    if (!strcmp(f, \"\\\\\")) return NI(~a.i); if (!strcmp(f, \"succ\")) return NI(a.i + 1);\n    if (!strcmp(f, \"msb\")) { long long x = a.i; int m = -1; while (x) { x >>= 1; m++; } return NI(m); }\n  } else if (t->arity == 2) {\n    Num a = eval(t->args[0]), b = eval(t->args[1]); int fl = a.f || b.f;\n    if (!strcmp(f, \"+\")) return fl ? NF(nd(a) + nd(b)) : NI(a.i + b.i);\n    if (!strcmp(f, \"-\")) return fl ? NF(nd(a) - nd(b)) : NI(a.i - b.i);\n    if (!strcmp(f, \"*\")) return fl ? NF(nd(a) * nd(b)) : NI(a.i * b.i);\n    if (!strcmp(f, \"/\")) { if (!fl) { if (b.i == 0) dl_die(\"division by zero\", NULL); if (a.i % b.i == 0) return NI(a.i / b.i); return NF((double)a.i / (double)b.i); } return NF(nd(a) / nd(b)); }\n    if (!strcmp(f, \"//\")) { if (b.i == 0) dl_die(\"division by zero\", NULL); return NI(a.i / b.i); }\n    if (!strcmp(f, \"div\")) { if (b.i == 0) dl_die(\"division by zero\", NULL); long long q = a.i / b.i; if ((a.i % b.i != 0) && ((a.i < 0) != (b.i < 0))) q--; return NI(q); }\n    if (!strcmp(f, \"mod\")) { if (b.i == 0) dl_die(\"division by zero\", NULL); long long m = a.i % b.i; if (m != 0 && ((m < 0) != (b.i < 0))) m += b.i; return NI(m); }\n    if (!strcmp(f, \"rem\")) { if (b.i == 0) dl_die(\"division by zero\", NULL); return NI(a.i % b.i); }\n    if (!strcmp(f, \"min\")) return nd(a) <= nd(b) ? a : b;\n    if (!strcmp(f, \"max\")) return nd(a) >= nd(b) ? a : b;\n    if (!strcmp(f, \"**\")) { if (!fl && b.i >= 0) { long long r = 1; for (long long k = 0; k < b.i; k++) r *= a.i; return NI(r); } return NF(pow(nd(a), nd(b))); }\n    if (!strcmp(f, \"^\")) { if (!fl) { if (b.i < 0) dl_die(\"^ with a negative exponent\", NULL); long long r = 1; for (long long k = 0; k < b.i; k++) r *= a.i; return NI(r); } return NF(pow(nd(a), nd(b))); }\n    if (!strcmp(f, \"atan2\") || !strcmp(f, \"atan\")) return NF(atan2(nd(a), nd(b)));\n    if (!strcmp(f, \">>\")) return NI(a.i >> b.i); if (!strcmp(f, \"<<\")) return NI(a.i << b.i);\n    if (!strcmp(f, \"/\\\\\")) return NI(a.i & b.i); if (!strcmp(f, \"\\\\/\")) return NI(a.i | b.i); if (!strcmp(f, \"xor\")) return NI(a.i ^ b.i);\n    if (!strcmp(f, \"gcd\")) { long long x = llabs(a.i), y = llabs(b.i); while (y) { long long r = x % y; x = y; y = r; } return NI(x); }\n    if (!strcmp(f, \"log\")) return NF(log(nd(b)) / log(nd(a)));\n  }\n  dl_die(\"not evaluable:\", f); return NI(0);\n}\nstatic Term *num_term(Num n) { return n.f ? mk_flt(n.d) : mk_int(n.i); }\nstatic int num_cmp(Term *a, Term *b) { Num x = eval(a), y = eval(b); if (!x.f && !y.f) return x.i < y.i ? -1 : x.i > y.i; double p = nd(x), q = nd(y); return p < q ? -1 : p > q; }\n\n/* ---------- builtins (deterministic) ---------- */\nstatic Term *list_of_chars(const char *s, int codes) { TV v = { 0 }; const unsigned char *p = (const unsigned char *)s;\n  while (*p) { int cp, n; if (*p < 0x80) { cp = *p; n = 1; } else if ((*p >> 5) == 6) { cp = ((*p & 31) << 6) | (p[1] & 63); n = 2; } else if ((*p >> 4) == 14) { cp = ((*p & 15) << 12) | ((p[1] & 63) << 6) | (p[2] & 63); n = 3; } else { cp = ((*p & 7) << 18) | ((p[1] & 63) << 12) | ((p[2] & 63) << 6) | (p[3] & 63); n = 4; }\n    if (codes) tv_push(&v, mk_int(cp)); else { char c[5]; memcpy(c, p, n); c[n] = 0; tv_push(&v, mk_atom(c)); } p += n; }\n  Term *r = tv_list(&v); tv_free(v.v); return r; }\nstatic size_t utf8_len(const char *s) { size_t n = 0; for (; *s; s++) if ((*s & 0xC0) != 0x80) n++; return n; }\nstatic int bi_length_det(Term **a) {\n  Term *l = deref(a[0]); long long n = 0;\n  while (is_cons(l)) { n++; l = deref(l->args[1]); }\n  if (is_nil(l)) return unify(a[1], mk_int(n));\n  if (l->tag != T_VAR) return 0;\n  Term *N = deref(a[1]); if (N->tag != T_INT) dl_die(\"length/2: infinite (both unbound)\", NULL);\n  if (N->iv < n) return 0; TV v = { 0 }; for (long long i = n; i < N->iv; i++) tv_push(&v, mk_var()); int ok = unify(l, tv_list(&v)); tv_free(v.v); return ok;\n}\nstatic int sort_cmp(const void *x, const void *y) { return compare(*(Term **)x, *(Term **)y); }\nstatic int bi_call(const char *k, Term **a); /* dispatch */\nstatic int sum_list(Term *l, Term **out) { TV v = { 0 }; if (!list_to_tv(l, &v)) dl_die(\"list expected\", NULL); Num s = NI(0);\n  for (size_t i = 0; i < v.n; i++) { Num x = eval(v.v[i]); s = (s.f || x.f) ? NF(nd(s) + nd(x)) : NI(s.i + x.i); } tv_free(v.v); *out = num_term(s); return 1; }\n\nstatic int bi_call(const char *k, Term **a) {\n  STEP();\n#define K(s) (k[0] == (s)[0] && k[1] == (s)[1] && !strcmp(k, s))\n  if (K(\"=/2\")) return unify(a[0], a[1]);\n  if (K(\"\\\\=/2\")) { size_t m = TR_TOP; int r = unify(a[0], a[1]); undo(m); return !r; }\n  if (K(\"==/2\")) return compare(a[0], a[1]) == 0;\n  if (K(\"\\\\==/2\")) return compare(a[0], a[1]) != 0;\n  if (K(\"@</2\")) return compare(a[0], a[1]) < 0;\n  if (K(\"@>/2\")) return compare(a[0], a[1]) > 0;\n  if (K(\"@=</2\")) return compare(a[0], a[1]) <= 0;\n  if (K(\"@>=/2\")) return compare(a[0], a[1]) >= 0;\n  if (K(\"compare/3\")) { int c = compare(a[1], a[2]); return unify(a[0], mk_atom(c < 0 ? \"<\" : c > 0 ? \">\" : \"=\")); }\n  if (K(\"is/2\")) return unify(a[0], num_term(eval(a[1])));\n  if (K(\"=:=/2\")) return num_cmp(a[0], a[1]) == 0;\n  if (K(\"=\\\\=/2\")) return num_cmp(a[0], a[1]) != 0;\n  if (K(\"</2\")) return num_cmp(a[0], a[1]) < 0;\n  if (K(\">/2\")) return num_cmp(a[0], a[1]) > 0;\n  if (K(\"=</2\")) return num_cmp(a[0], a[1]) <= 0;\n  if (K(\">=/2\")) return num_cmp(a[0], a[1]) >= 0;\n  if (K(\"true/0\")) return 1;\n  if (K(\"fail/0\") || K(\"false/0\")) return 0;\n  if (K(\"var/1\")) return deref(a[0])->tag == T_VAR;\n  if (K(\"nonvar/1\")) return deref(a[0])->tag != T_VAR;\n  if (K(\"atom/1\")) return deref(a[0])->tag == T_ATOM;\n  if (K(\"number/1\")) { int g = deref(a[0])->tag; return g == T_INT || g == T_FLT; }\n  if (K(\"integer/1\")) return deref(a[0])->tag == T_INT;\n  if (K(\"float/1\")) return deref(a[0])->tag == T_FLT;\n  if (K(\"atomic/1\")) { int g = deref(a[0])->tag; return g != T_VAR && g != T_CMP; }\n  if (K(\"compound/1\")) return deref(a[0])->tag == T_CMP;\n  if (K(\"callable/1\")) { int g = deref(a[0])->tag; return g == T_ATOM || g == T_CMP; }\n  if (K(\"string/1\")) return deref(a[0])->tag == T_STR;\n  if (K(\"is_list/1\")) { TV v = { 0 }; int r = list_to_tv(a[0], &v); tv_free(v.v); return r; }\n  if (K(\"ground/1\")) return is_ground(a[0]);\n  if (K(\"copy_term/2\")) return unify(a[1], copy_term(a[0]));\n  if (K(\"functor/3\")) { Term *t = deref(a[0]);\n    if (t->tag == T_VAR) { Term *n = deref(a[2]), *f = deref(a[1]); if (n->iv == 0) return unify(t, f); TV v = { 0 }; for (long long i = 0; i < n->iv; i++) tv_push(&v, mk_var()); int r = unify(t, mk_cmp(f->name, (int)n->iv, v.v)); tv_free(v.v); return r; }\n    if (t->tag == T_CMP) return unify(a[1], mk_atom(t->name)) && unify(a[2], mk_int(t->arity));\n    return unify(a[1], t) && unify(a[2], mk_int(0)); }\n  if (K(\"arg/3\")) { Term *n = deref(a[0]), *t = deref(a[1]); if (n->tag != T_INT) dl_die(\"arg/3 with unbound index needs builtin_rows\", NULL); if (t->tag != T_CMP || n->iv < 1 || n->iv > t->arity) return 0; return unify(a[2], t->args[n->iv - 1]); }\n  if (K(\"=../2\")) { Term *t = deref(a[0]);\n    if (t->tag == T_CMP) { TV v = { 0 }; tv_push(&v, mk_atom(t->name)); for (int i = 0; i < t->arity; i++) tv_push(&v, t->args[i]); int r = unify(a[1], tv_list(&v)); tv_free(v.v); return r; }\n    if (t->tag != T_VAR) return unify(a[1], mk_cons(t, NIL));\n    TV v = { 0 }; if (!list_to_tv(a[1], &v)) dl_die(\"=..: list expected\", NULL); Term *h = deref(v.v[0]); int r = v.n == 1 ? unify(t, h) : unify(t, mk_cmp(h->name, (int)v.n - 1, v.v + 1)); tv_free(v.v); return r; }\n  if (K(\"succ/2\")) { Term *x = deref(a[0]); if (x->tag == T_INT) return unify(a[1], mk_int(x->iv + 1)); Term *y = deref(a[1]); if (y->iv <= 0) return 0; return unify(x, mk_int(y->iv - 1)); }\n  if (K(\"plus/3\")) { Term *x = deref(a[0]), *y = deref(a[1]), *z = deref(a[2]);\n    if (x->tag == T_INT && y->tag == T_INT) return unify(z, mk_int(x->iv + y->iv)); if (x->tag == T_INT) return unify(y, mk_int(z->iv - x->iv)); return unify(x, mk_int(z->iv - y->iv)); }\n  if (K(\"length/2\")) return bi_length_det(a);\n  if (K(\"reverse/2\")) { TV v = { 0 }; if (!list_to_tv(a[0], &v)) return 0; Term *r = NIL; for (size_t i = 0; i < v.n; i++) r = mk_cons(v.v[i], r); tv_free(v.v); return unify(a[1], r); }\n  if (K(\"msort/2\") || K(\"sort/2\")) { TV v = { 0 }; if (!list_to_tv(a[0], &v)) dl_die(\"sort: list expected\", NULL); qsort(v.v, v.n, sizeof(Term *), sort_cmp);\n    if (K(\"sort/2\")) { size_t o = 0; for (size_t i = 0; i < v.n; i++) if (!o || compare(v.v[o - 1], v.v[i])) v.v[o++] = v.v[i]; v.n = o; }\n    int r = unify(a[1], tv_list(&v)); tv_free(v.v); return r; }\n  if (K(\"sum_list/2\") || K(\"sumlist/2\")) { Term *s; sum_list(a[0], &s); return unify(a[1], s); }\n  if (K(\"max_list/2\") || K(\"min_list/2\")) { TV v = { 0 }; list_to_tv(a[0], &v); if (!v.n) return 0; Num m = eval(v.v[0]); int mx = K(\"max_list/2\");\n    for (size_t i = 1; i < v.n; i++) { Num x = eval(v.v[i]); if (mx ? nd(x) > nd(m) : nd(x) < nd(m)) m = x; } tv_free(v.v); return unify(a[1], num_term(m)); }\n  if (K(\"nth0/3\") || K(\"nth1/3\")) { Term *i = deref(a[0]); if (i->tag != T_INT) dl_die(\"nth: unbound index needs builtin_rows\", NULL); TV v = { 0 }; list_to_tv(a[1], &v); long long base = K(\"nth1/3\") ? 1 : 0; long long k = i->iv - base; /* base first: K() reads the predicate key, which this k would shadow */ int r = k >= 0 && k < (long long)v.n && unify(a[2], v.v[k]); tv_free(v.v); return r; }\n  if (K(\"last/2\")) { TV v = { 0 }; list_to_tv(a[0], &v); int r = v.n && unify(a[1], v.v[v.n - 1]); tv_free(v.v); return r; }\n  if (K(\"memberchk/2\")) { Term *l = deref(a[1]); while (is_cons(l)) { size_t m = TR_TOP; if (unify(a[0], l->args[0])) return 1; undo(m); l = deref(l->args[1]); } return 0; }\n  if (K(\"numlist/3\")) { long long lo = eval(a[0]).i, hi = eval(a[1]).i; Term *r = NIL; for (long long i = hi; i >= lo; i--) r = mk_gcons(mk_int(i), r); return unify(a[2], r); }\n  if (K(\"atom_length/2\") || K(\"string_length/2\")) return unify(a[1], mk_int((long long)utf8_len(text_of(a[0]))));\n  if (K(\"atom_codes/2\") || K(\"atom_chars/2\") || K(\"string_codes/2\") || K(\"string_chars/2\")) { Term *t = deref(a[0]); int codes = strstr(k, \"codes\") != NULL; int str = !strncmp(k, \"string\", 6);\n    if (t->tag != T_VAR) return unify(a[1], list_of_chars(text_of(t), codes)); return unify(t, str ? mk_str(text_of(a[1])) : mk_atom(text_of(a[1]))); }\n  if (K(\"char_code/2\")) { Term *t = deref(a[0]); if (t->tag == T_ATOM) { Term *l = list_of_chars(t->name, 1); return unify(a[1], deref(l)->args[0]); } char c[2] = { (char)deref(a[1])->iv, 0 }; return unify(t, mk_atom(c)); }\n  if (K(\"atom_number/2\")) { Term *t = deref(a[0]); if (t->tag == T_VAR) return unify(t, mk_atom(show_term(a[1], 0))); char *s = text_of(t); char *e; long long iv = strtoll(s, &e, 10); if (*s && !*e) return unify(a[1], mk_int(iv)); double d = strtod(s, &e); if (*s && !*e) return unify(a[1], mk_flt(d)); return 0; }\n  if (K(\"number_codes/2\")) { Term *t = deref(a[0]); if (t->tag != T_VAR) return unify(a[1], list_of_chars(show_term(t, 0), 1)); char *s = text_of(a[1]); char *e; long long iv = strtoll(s, &e, 10); if (*s && !*e) return unify(t, mk_int(iv)); return unify(t, mk_flt(strtod(s, NULL))); }\n  if (K(\"atom_string/2\")) { Term *t = deref(a[0]); if (t->tag != T_VAR) return unify(a[1], mk_str(text_of(t))); return unify(t, mk_atom(text_of(a[1]))); }\n  if (K(\"string_concat/3\")) { SB b = { 0 }; sb_puts(&b, text_of(a[0])); sb_puts(&b, text_of(a[1])); return unify(a[2], mk_str(b.s)); }\n  if (K(\"atomic_list_concat/2\") || K(\"atomic_list_concat/3\")) { TV v = { 0 }; list_to_tv(a[0], &v); SB b = { 0 }; sb_puts(&b, \"\"); const char *sep = K(\"atomic_list_concat/3\") ? text_of(a[1]) : \"\";\n    for (size_t i = 0; i < v.n; i++) { if (i) sb_puts(&b, sep); sb_puts(&b, text_of(v.v[i])); } tv_free(v.v); return unify(a[K(\"atomic_list_concat/3\") ? 2 : 1], mk_atom(b.s)); }\n  if (K(\"upcase_atom/2\") || K(\"downcase_atom/2\")) { char *s = text_of(a[0]); for (char *p = s; *p; p++) *p = K(\"upcase_atom/2\") ? (char)toupper((unsigned char)*p) : (char)tolower((unsigned char)*p); return unify(a[1], mk_atom(s)); }\n  if (K(\"term_to_atom/2\")) return unify(a[1], mk_atom(show_term(a[0], 1)));\n  if (K(\"code_type/2\")) { Term *c = deref(a[0]); int ch = c->tag == T_INT ? (int)c->iv : (unsigned char)c->name[0]; Term *ty = deref(a[1]); const char *tn = ty->name;\n    if (!strcmp(tn, \"digit\") && ty->tag == T_CMP) return isdigit(ch) && unify(ty->args[0], mk_int(ch - '0'));\n    if (!strcmp(tn, \"digit\")) return isdigit(ch) != 0; if (!strcmp(tn, \"alpha\")) return isalnum(ch) || ch == '_'; if (!strcmp(tn, \"alnum\")) return isalnum(ch) != 0;\n    if (!strcmp(tn, \"space\") || !strcmp(tn, \"white\")) return isspace(ch) != 0; if (!strcmp(tn, \"upper\")) return isupper(ch) != 0; if (!strcmp(tn, \"lower\")) return islower(ch) != 0;\n    if (!strcmp(tn, \"punct\")) return ispunct(ch) != 0; if (!strcmp(tn, \"csym\")) return isalnum(ch) || ch == '_'; if (!strcmp(tn, \"csymf\")) return isalpha(ch) || ch == '_'; return 0; }\n  if (K(\"split_string/4\")) { char *s = text_of(a[0]), *sep = text_of(a[1]), *pad = text_of(a[2]); TV parts = { 0 }; SB cur = { 0 }; sb_puts(&cur, \"\");\n    for (char *p = s;; p++) { if (*p == 0 || (*sep && strchr(sep, *p))) { char *x = cur.s; size_t n = strlen(x); size_t i = 0; while (i < n && *pad && strchr(pad, x[i])) i++; while (n > i && *pad && strchr(pad, x[n - 1])) n--; x[n] = 0; tv_push(&parts, mk_str(x + i)); cur.s = NULL; cur.n = cur.cap = 0; sb_puts(&cur, \"\"); if (!*p) break; } else sb_putc(&cur, *p); }\n    int r = unify(a[3], tv_list(&parts)); tv_free(parts.v); return r; }\n  if (K(\"throw/1\")) dl_die(\"uncaught exception:\", show_term(a[0], 1));\n#undef K\n  dl_die(\"builtin not available in the C runtime:\", k); return 0;\n}\n\n/* ---------- output effects ---------- */\nstatic void format_into(SB *b, const char *f, Term *args) {\n  TV v = { 0 }; if (!list_to_tv(args, &v)) { tv_push(&v, args); } size_t ai = 0;\n  for (const char *p = f; *p; p++) {\n    if (*p != '~') { sb_putc(b, *p); continue; }\n    p++; int n = -1; while (*p >= '0' && *p <= '9') { n = (n < 0 ? 0 : n * 10) + (*p - '0'); p++; }\n    switch (*p) {\n      case 'w': { char *s = show_w(v.v[ai++], 0); sb_puts(b, s); free(s); break; }\n      case 'p': { char *s = show_w(v.v[ai++], SWIQ); sb_puts(b, s); free(s); break; }\n      case 'q': { char *s = show_w(v.v[ai++], 1); sb_puts(b, s); free(s); break; }\n      case 'a': case 's': sb_puts(b, text_of(v.v[ai++])); break;\n      case 'd': { char t[32]; snprintf(t, sizeof t, \"%lld\", deref(v.v[ai++])->iv); sb_puts(b, t); break; }\n      case 'f': { char t[64]; snprintf(t, sizeof t, \"%.*f\", n < 0 ? 6 : n, nd(eval(v.v[ai++]))); sb_puts(b, t); break; }\n      case 'e': { char t[64]; snprintf(t, sizeof t, \"%.*e\", n < 0 ? 6 : n, nd(eval(v.v[ai++]))); sb_puts(b, t); break; }\n      case 'n': { int k = n < 0 ? 1 : n; while (k--) sb_putc(b, '\\n'); break; }\n      case 'c': { int k = n < 0 ? 1 : n; while (k--) sb_putc(b, (char)deref(v.v[ai])->iv); ai++; break; }\n      case '~': sb_putc(b, '~'); break;\n      case 't': case '|': case '+': break;\n      default: sb_putc(b, '~'); sb_putc(b, *p);\n    }\n  }\n  tv_free(v.v);\n}\nstatic int rt_effect_text(Term *g, Term *T) {\n  STEP(); g = deref(g); SB b = { 0 }; sb_puts(&b, \"\");\n  const char *f = g->name; int n = g->tag == T_CMP ? g->arity : 0; Term **a = g->args;\n  if (!strcmp(f, \"write\") && n == 1) { char *s = show_w(a[0], 0); sb_puts(&b, s); }\n  else if (!strcmp(f, \"print\") && n == 1) { char *s = show_w(a[0], 1); sb_puts(&b, s); }\n  else if (!strcmp(f, \"writeq\") && n == 1) { char *s = show_w(a[0], 1); sb_puts(&b, s); }\n  else if (!strcmp(f, \"write_canonical\") && n == 1) { char *s = show_w(a[0], 1); sb_puts(&b, s); }\n  else if (!strcmp(f, \"write_term\") && n == 2) { char *s = show_w(a[0], 0); sb_puts(&b, s); }\n  else if (!strcmp(f, \"writeln\") && n == 1) { char *s = show_w(a[0], 0); sb_puts(&b, s); sb_putc(&b, '\\n'); }\n  else if (!strcmp(f, \"nl\") && n == 0) sb_putc(&b, '\\n');\n  else if (!strcmp(f, \"tab\") && n == 1) { long long k = eval(a[0]).i; while (k-- > 0) sb_putc(&b, ' '); }\n  else if (!strcmp(f, \"put_char\") && n == 1) sb_puts(&b, deref(a[0])->name);\n  else if (!strcmp(f, \"format\") && n == 1) format_into(&b, text_of(a[0]), NIL);\n  else if (!strcmp(f, \"format\") && n == 2) format_into(&b, text_of(a[0]), a[1]);\n  else if (!strcmp(f, \"format\") && n == 3) format_into(&b, text_of(a[1]), a[2]);\n  else if (!strcmp(f, \"flush_output\") && n == 0) { }\n  else dl_die(\"effect_text: unsupported output builtin\", f);\n  return unify(T, mk_str(b.s));\n}\n\n/* ---------- packets ---------- */\nstatic int is_out(Term *t) { t = deref(t); return t->tag == T_CMP && t->arity == 1 && t->name == A_OUT->name; }\nstatic int is_row(Term *t) { t = deref(t); return t->tag == T_CMP && t->arity == 1 && t->name == A_E->name; }\nstatic Term *A_CUT;\nstatic TV items(Term *t) { TV v = { 0 }; if (!list_to_tv(t, &v)) dl_die(\"packet is not a proper list\", NULL); return v; }\nstatic int is_cut(Term *t) { return deref(t) == A_CUT; }\nstatic int has_cut(TV *v) { for (size_t i = 0; i < v->n; i++) if (is_cut(v->v[i])) return 1; return 0; }\n/* cut markers: rows_concat_cut keeps markers and stops after a list containing one; rows_cut_concat also strips them */\nstatic int rt_concat_cut(Term *ls, Term *out, int strip) {\n  TV L = items(ls), all = { 0 };\n  for (size_t i = 0; i < L.n; i++) { TV x = items(L.v[i]); for (size_t j = 0; j < x.n; j++) { STEP(); if (!(strip && is_cut(x.v[j]))) tv_push(&all, x.v[j]); } int c = has_cut(&x); tv_free(x.v); if (c) break; }\n  int r = unify(out, tv_list(&all)); tv_free(L.v); tv_free(all.v); return r;\n}\nstatic int rt_rows_concat_cut(Term *ls, Term *out) { return rt_concat_cut(ls, out, 0); }\nstatic int rt_rows_cut_concat(Term *ls, Term *out) { return rt_concat_cut(ls, out, 1); }\nstatic int rt_strip_cut(Term *R, Term *out) { Term *l[1] = { R }; return rt_concat_cut(tv_list(&(TV){ l, 1, 1 }), out, 1); }\nstatic int rt_cut_in(Term *I, Term *O) { if (!is_row(I)) return 0; TV x = items(O); int c = has_cut(&x); tv_free(x.v); return c; }\nstatic Term *mk_e(Term *x) { return mk_cmp(A_E->name, 1, &x); }\nstatic Term *pair(Term *a, Term *b) { Term *x[2] = { a, b }; return mk_cmp(A_MINUS->name, 2, x); }\nstatic int rt_rows_concat(Term *ls, Term *out) {\n  TV L = items(ls), all = { 0 };\n  for (size_t i = 0; i < L.n; i++) { TV x = items(L.v[i]); for (size_t j = 0; j < x.n; j++) { STEP(); tv_push(&all, x.v[j]); } tv_free(x.v); }\n  int r = unify(out, tv_list(&all)); tv_free(L.v); tv_free(all.v); return r;\n}\nstatic int ground_eq(Term *a, Term *b) {\n  a = deref(a); b = deref(b); if (a == b) return 1; if (a->tag != b->tag) return 0;\n  switch (a->tag) {\n    case T_INT: return a->iv == b->iv; case T_FLT: return a->fv == b->fv; case T_STR: return !strcmp(a->name, b->name); case T_ATOM: return a->name == b->name;\n    case T_CMP: if (a->name != b->name || a->arity != b->arity) return 0; for (int i = 0; i < a->arity; i++) if (!ground_eq(a->args[i], b->args[i])) return 0; return 1;\n  }\n  return 0;\n}\n/* splice_extend with a simple pattern: a list of distinct unbound variables and ground terms, and an\n   environment whose variables are all pattern variables. Matching a ground row against it binds each\n   pattern variable to the row's value, so the copy and unification the general case makes per row come\n   down to comparing the ground positions and putting the row's values into the environment's shape. */\nstatic Term *sp_subst(Term *t, Term **pv, Term **rv, int n) {\n  t = deref(t);\n  if (t->tag == T_VAR) { for (int i = 0; i < n; i++) if (pv[i] == t) return rv[i]; return NULL; }\n  if (t->tag != T_CMP || t->cpe == GR_MARK) return t;\n  Term *a[16]; if (t->arity > 16) return NULL;\n  for (int i = 0; i < t->arity; i++) if (!(a[i] = sp_subst(t->args[i], pv, rv, n))) return NULL;\n  return is_cons(t) ? mk_cons(a[0], a[1]) : mk_cmp(t->name, t->arity, a);\n}\nstatic int sp_env_ok(Term *t, Term **pv, int n) {\n  t = deref(t);\n  if (t->tag == T_VAR) { for (int i = 0; i < n; i++) if (pv[i] == t) return 1; return 0; }\n  if (t->tag != T_CMP || t->cpe == GR_MARK) return 1;\n  if (t->arity > 16) return 0;\n  for (int i = 0; i < t->arity; i++) if (!sp_env_ok(t->args[i], pv, n)) return 0;\n  return 1;\n}\nstatic int rt_splice_extend_generic(Term *P, Term *pat, Term *env, Term *O);\nstatic int rt_splice_extend(Term *P, Term *pat, Term *env, Term *O) {\n  Term *ps[16], *pv[16]; int np = 0, nv = 0, simple = 1; Term *x = deref(pat);\n  int pvi[16];\n  while (is_cons(x) && simple) { if (np == 16) { simple = 0; break; } Term *h = deref(x->args[0]);\n    if (h->tag == T_VAR) { for (int i = 0; i < nv; i++) if (pv[i] == h) simple = 0; pvi[nv] = np; pv[nv++] = h; } else if (!is_ground(h)) simple = 0;\n    ps[np++] = h; x = deref(x->args[1]); }\n  if (!simple || !is_nil(x) || !sp_env_ok(env, pv, nv)) return rt_splice_extend_generic(P, pat, env, O);\n  Term *loc[64]; Term **res = loc; size_t n = 0, cap = 64; Term *p = deref(P);\n  while (is_cons(p)) {\n    Term *r = deref(p->args[0]); p = deref(p->args[1]); Term *out;\n    if (is_out(r) || is_cut(r)) out = r;\n    else {\n      Term *rv[16], *y = deref(r->args[0]); int k = 0, ok = 1, gen = 0;\n      for (; k < np && is_cons(y); k++, y = deref(y->args[1])) { Term *v = deref(y->args[0]); if (!GND(v) && !is_ground(v)) { gen = 1; break; } if (ps[k]->tag != T_VAR && !ground_eq(ps[k], v)) { ok = 0; break; } }\n      if (gen || (ok && (k != np || !is_nil(y)))) { if (res != loc) free(res); return rt_splice_extend_generic(P, pat, env, O); }\n      if (!ok) continue;\n      y = deref(r->args[0]); for (int i = 0, j = 0; i < np; i++, y = deref(y->args[1])) if (j < nv && pvi[j] == i) rv[j++] = deref(y->args[0]);\n      out = sp_subst(env, pv, rv, nv);\n    }\n    if (n == cap) { Term **nr = (Term **)malloc(sizeof(Term *) * cap * 2); memcpy(nr, res, sizeof(Term *) * n); if (res != loc) free(res); res = nr; cap *= 2; }\n    res[n++] = out;\n  }\n  if (!is_nil(p)) { if (res != loc) free(res); return rt_splice_extend_generic(P, pat, env, O); }\n  Term *l = NIL; for (size_t i = n; i-- > 0;) l = mk_cons(res[i], l);\n  if (res != loc) free(res);\n  return unify(O, l);\n}\nstatic int rt_splice_extend_generic(Term *P, Term *pat, Term *env, Term *O) {\n  TV it = items(P), res = { 0 };\n  for (size_t i = 0; i < it.n; i++) {\n    STEP(); Term *x = deref(it.v[i]);\n    if (is_out(x) || is_cut(x)) { tv_push(&res, x); continue; }\n    Term *c = copy_term(pair(pat, env)); size_t m = TR_TOP;\n    if (unify(c->args[0], x->args[0])) tv_push(&res, resolve(c->args[1]));\n    undo(m);\n  }\n  int r = unify(O, tv_list(&res)); tv_free(it.v); tv_free(res.v); return r;\n}\nstatic int rt_project_rows(Term *R, Term *vs, Term *h, Term *Rows) {\n  TV it = items(R), res = { 0 };\n  for (size_t i = 0; i < it.n; i++) {\n    STEP(); Term *x = deref(it.v[i]);\n    if (is_out(x) || is_cut(x)) { tv_push(&res, x); continue; }\n    Term *c = copy_term(pair(vs, h)); size_t m = TR_TOP;\n    if (unify(c->args[0], x->args[0])) tv_push(&res, mk_e(resolve(c->args[1])));\n    undo(m);\n  }\n  int r = unify(Rows, tv_list(&res)); tv_free(it.v); tv_free(res.v); return r;\n}\nstatic int rt_project_list(Term *R, Term *eg, Term *tg, Term *Ts) {\n  TV it = items(R), res = { 0 };\n  for (size_t i = 0; i < it.n; i++) {\n    STEP(); Term *x = deref(it.v[i]); if (!is_row(x)) continue;\n    Term *c = copy_term(pair(eg, tg)); size_t m = TR_TOP;\n    if (unify(c->args[0], x)) tv_push(&res, resolve(c->args[1]));\n    undo(m);\n  }\n  int r = unify(Ts, tv_list(&res)); tv_free(it.v); tv_free(res.v); return r;\n}\nstatic int rt_packet_first(Term *R, Term *Pre, Term *First) {\n  TV it = items(R), pre = { 0 }; int r;\n  for (size_t i = 0; i < it.n; i++) { STEP(); if (is_cut(it.v[i])) continue; if (is_out(it.v[i])) { tv_push(&pre, deref(it.v[i])); continue; }\n    r = unify(Pre, tv_list(&pre)) && unify(First, mk_cons(it.v[i], NIL)); tv_free(it.v); tv_free(pre.v); return r; }\n  r = unify(Pre, tv_list(&pre)) && unify(First, NIL); tv_free(it.v); tv_free(pre.v); return r;\n}\nstatic int rt_packet_split(Term *R, Term *Outs, Term *Rows) {\n  TV it = items(R), o = { 0 }, w = { 0 };\n  for (size_t i = 0; i < it.n; i++) { STEP(); if (is_cut(it.v[i])) continue; if (is_out(it.v[i])) tv_push(&o, deref(it.v[i])); else tv_push(&w, deref(it.v[i])); }\n  int r = unify(Outs, tv_list(&o)) && unify(Rows, tv_list(&w)); tv_free(it.v); tv_free(o.v); tv_free(w.v); return r;\n}\nstatic int rt_cp_filter(Term *F, Term *pat, Term *Rows) {\n  TV it = items(F), res = { 0 };\n  for (size_t i = 0; i < it.n; i++) {\n    STEP(); Term *c = copy_term(pat); Term *f = copy_term(deref(it.v[i])->args[0]); size_t m = TR_TOP;\n    if (unify(c, f)) tv_push(&res, mk_e(resolve(c)));\n    undo(m);\n  }\n  int r = unify(Rows, tv_list(&res)); tv_free(it.v); tv_free(res.v); return r;\n}\nstatic int rt_aggregate_list(Term *S, Term *Ts, Term *R) {\n  const char *sp = deref(S)->name; TV v = items(Ts); Term *r = NULL;\n  if (!strcmp(sp, \"count\")) r = mk_int((long long)v.n);\n  else if (!strcmp(sp, \"sum\")) sum_list(Ts, &r);\n  else if (!strcmp(sp, \"max\") || !strcmp(sp, \"min\")) { if (!v.n) { tv_free(v.v); return 0; } Num m = eval(v.v[0]); for (size_t i = 1; i < v.n; i++) { Num x = eval(v.v[i]); if (!strcmp(sp, \"max\") ? nd(x) > nd(m) : nd(x) < nd(m)) m = x; } r = num_term(m); }\n  else if (!strcmp(sp, \"bag\")) r = Ts;\n  else if (!strcmp(sp, \"set\")) { Term *a[2] = { Ts, mk_var() }; bi_call(\"sort/2\", a); r = a[1]; }\n  else dl_die(\"aggregate_list: unknown spec\", sp);\n  tv_free(v.v); return unify(R, r);\n}\nstatic int rt_splice_safe(Term *A, Term *B) {\n  TV va = { 0 }, vb = { 0 }; term_vars(A, &va); term_vars(B, &vb); int ok = 1;\n  for (size_t i = 0; i < va.n && ok; i++) for (size_t j = 0; j < vb.n; j++) if (va.v[i] == vb.v[j]) { ok = 0; break; }\n  tv_free(va.v); tv_free(vb.v); return ok;\n}\nstatic int rt_splice2(Term *PA, Term *PB, Term *pa, Term *pb, Term *env, Term *O) {\n  TV A = items(PA), B = items(PB), res = { 0 };\n  for (size_t i = 0; i < A.n; i++) {\n    if (is_out(A.v[i])) { tv_push(&res, deref(A.v[i])); continue; }\n    for (size_t j = 0; j < B.n; j++) {\n      STEP(); if (is_out(B.v[j])) continue;\n      Term *x[3] = { pa, pb, env }; Term *c = copy_term(mk_cmp(intern(\"f\"), 3, x)); size_t m = TR_TOP;\n      if (unify(c->args[0], deref(A.v[i])->args[0]) && unify(c->args[1], deref(B.v[j])->args[0])) tv_push(&res, resolve(c->args[2]));\n      undo(m);\n    }\n  }\n  int r = unify(O, tv_list(&res)); tv_free(A.v); tv_free(B.v); tv_free(res.v); return r;\n}\n/* memo: variant key -> stored f(Args, Rows) */\ntypedef struct ME { char *key; Term *val; struct ME *next; } ME;\n#define MH 65536\nstatic ME *memo[MH];\n/* buckets in use, so that clearing the table between runs costs what was stored, not the table size */\nstatic unsigned *memo_used = NULL; static size_t memo_nused = 0, memo_cap = 0;\nstatic void memo_clear(void) {\n  for (size_t i = 0; i < memo_nused; i++) { ME *e = memo[memo_used[i]]; while (e) { ME *n = e->next; free(e->key); free(e); e = n; } memo[memo_used[i]] = NULL; }\n  memo_nused = 0;\n}\nstatic void vkey(SB *b, Term *t, TV *vs) {\n  t = deref(t); char buf[64];\n  switch (t->tag) {\n    case T_VAR: { size_t i; for (i = 0; i < vs->n; i++) if (vs->v[i] == t) break; if (i == vs->n) tv_push(vs, t); snprintf(buf, sizeof buf, \"_%zu \", i); sb_puts(b, buf); return; }\n    case T_INT: snprintf(buf, sizeof buf, \"i%lld \", t->iv); sb_puts(b, buf); return;\n    case T_FLT: snprintf(buf, sizeof buf, \"f%.17g \", t->fv); sb_puts(b, buf); return;\n    case T_ATOM: sb_puts(b, \"a\"); sb_puts(b, t->name); sb_puts(b, \"\\x01\"); return;\n    case T_STR: sb_puts(b, \"s\"); sb_puts(b, t->name); sb_puts(b, \"\\x01\"); return;\n    default: sb_puts(b, \"c\"); sb_puts(b, t->name); snprintf(buf, sizeof buf, \"/%d(\", t->arity); sb_puts(b, buf); for (int i = 0; i < t->arity; i++) vkey(b, t->args[i], vs); sb_puts(b, \")\"); return;\n  }\n}\nstatic char *variant_key(Term *k, Term *args) { SB b = { 0 }; TV vs = { 0 }; vkey(&b, k, &vs); vkey(&b, args, &vs); tv_free(vs.v); return b.s; }\nstatic int rt_memo_lookup(Term *K, Term *Args, Term *Found) {\n  STEP(); char *key = variant_key(K, Args); unsigned long h = hstr(key) % MH;\n  for (ME *e = memo[h]; e; e = e->next) if (!strcmp(e->key, key)) {\n    free(key); dl_memo_hits++;\n    Term *c = copy_term(e->val); TV sv = { 0 }, cv = { 0 }; term_vars(c->args[0], &sv); term_vars(Args, &cv);\n    for (size_t i = 0; i < sv.n && i < cv.n; i++) sv.v[i]->ref = cv.v[i];\n    Term *r = resolve(c->args[1]); for (size_t i = 0; i < sv.n; i++) sv.v[i]->ref = NULL; tv_free(sv.v); tv_free(cv.v);\n    return unify(Found, mk_cmp(A_FOUND->name, 1, &r));\n  }\n  free(key); return unify(Found, A_NONE);\n}\nstatic int rt_memo_store(Term *K, Term *Args, Term *Rows) {\n  char *key = variant_key(K, Args); unsigned long h = hstr(key) % MH;\n  for (ME *e = memo[h]; e; e = e->next) if (!strcmp(e->key, key)) { free(key); return 1; }\n  if (!memo[h]) { if (memo_nused == memo_cap) { memo_cap = memo_cap ? memo_cap * 2 : 64; memo_used = (unsigned *)realloc(memo_used, memo_cap * sizeof(unsigned)); } memo_used[memo_nused++] = (unsigned)h; }\n  ME *e = (ME *)malloc(sizeof(ME)); e->key = key; e->val = copy_term(pair(Args, Rows)); e->next = memo[h]; memo[h] = e; return 1;\n}\nstatic long long binom(long long n, int k) { double r = 1; for (int i = 0; i < k; i++) r = r * (double)(n - i) / (double)(i + 1); return llround(r); }\nstatic int rt_s2a_rows_generic(Term *spec, Term *args, Term *Rows) {\n  spec = deref(spec); long long K = deref(spec->args[0])->iv; TV cols = items(spec->args[1]), as = items(args), res = { 0 };\n  long long only = -2;\n  for (size_t j = 0; j < cols.n; j++) { Term *c = deref(cols.v[j]), *x = deref(as.v[j]);\n    if (!strcmp(c->name, \"newton\") && x->tag == T_INT) { TV ds = items(c->args[0]); if (ds.n == 2 && deref(ds.v[1])->iv != 0) { long long d0 = deref(ds.v[0])->iv, d1 = deref(ds.v[1])->iv; only = ((x->iv - d0) % d1 == 0 && (x->iv - d0) / d1 >= 0 && (x->iv - d0) / d1 < K) ? (x->iv - d0) / d1 : -1; tv_free(ds.v); break; } tv_free(ds.v); } }\n  long long lo = 0, hi = K; if (only == -1) hi = 0; else if (only >= 0) { lo = only; hi = only + 1; }\n  for (long long I = lo; I < hi; I++) {\n    STEP(); TV row = { 0 };\n    for (size_t j = 0; j < cols.n; j++) { Term *c = deref(cols.v[j]);\n      if (!strcmp(c->name, \"const\")) tv_push(&row, c->args[0]);\n      else if (!strcmp(c->name, \"data\")) { TV d = items(c->args[0]); tv_push(&row, d.v[I]); tv_free(d.v); }\n      else { TV ds = items(c->args[0]); long long s = 0; for (size_t d = 0; d < ds.n; d++) s += deref(ds.v[d])->iv * binom(I, (int)d); tv_free(ds.v); tv_push(&row, mk_int(s)); } }\n    Term *c = copy_term(args); size_t m = TR_TOP;\n    if (unify(c, tv_list(&row))) tv_push(&res, mk_e(resolve(c)));\n    undo(m); tv_free(row.v);\n  }\n  int r = unify(Rows, tv_list(&res)); tv_free(cols.v); tv_free(as.v); tv_free(res.v); return r;\n}\n/* An S2A table is constant: its rows are built once, as ground terms, and kept (startup work, not\n   per-query work). A call whose arguments are each a distinct unbound variable or a ground term only\n   picks the rows that match (structural equality is unification for ground terms); with every argument\n   unbound, the packet itself is kept and returned. Any other call (a repeated variable, a partly bound\n   argument) builds the rows as before. */\ntypedef struct { Term *spec; size_t n, ncols; Term **cells; Term **rows; Term *all; } S2ATab;\nstatic S2ATab s2a_tabs[64]; static int s2a_ntabs = 0;\n/* a full copy of a ground term (call with pinned set: it then outlives the run's arena) */\nstatic Term *pin_copy(Term *t) {\n  t = deref(t);\n  switch (t->tag) {\n    case T_ATOM: return t;\n    case T_INT: return mk_int(t->iv); case T_FLT: return mk_flt(t->fv); case T_STR: return mk_str(t->name);\n    case T_CMP: { Term **a = (Term **)alloc(sizeof(Term *) * t->arity); for (int i = 0; i < t->arity; i++) a[i] = pin_copy(t->args[i]); Term *r = new_term(T_CMP); r->name = t->name; r->arity = t->arity; r->args = a; r->cpe = GR_MARK; return r; }\n  }\n  dl_die(\"s2a row is not ground\", NULL); return t;\n}\nstatic S2ATab *s2a_tab(Term *spec, size_t ncols) {\n  for (int i = 0; i < s2a_ntabs; i++) if (s2a_tabs[i].spec == spec) return &s2a_tabs[i];\n  if (s2a_ntabs == 64) return NULL;\n  /* the rows, from the generic code with fresh variables, then kept outside the arena */\n  TV vs = { 0 }; for (size_t j = 0; j < ncols; j++) tv_push(&vs, mk_var());\n  Term *args = tv_list(&vs), *R = mk_var(); size_t m = TR_TOP;\n  if (!rt_s2a_rows_generic(spec, args, R)) { undo(m); tv_free(vs.v); return NULL; }\n  TV rows = items(R);\n  S2ATab *t = &s2a_tabs[s2a_ntabs++]; t->spec = spec; t->n = rows.n; t->ncols = ncols;\n  t->cells = (Term **)malloc(sizeof(Term *) * (rows.n * ncols + 1)); t->rows = (Term **)malloc(sizeof(Term *) * (rows.n + 1));\n  for (size_t i = 0; i < rows.n; i++) { Term *e = deref(rows.v[i]); t->rows[i] = e; TV c = items(deref(e)->args[0]); for (size_t j = 0; j < ncols; j++) t->cells[i * ncols + j] = c.v[j]; tv_free(c.v); }\n  pinned = 1; t->all = pin_copy(R); TV pr = items(t->all); for (size_t i = 0; i < rows.n; i++) { t->rows[i] = deref(pr.v[i]); TV c = items(deref(t->rows[i])->args[0]); for (size_t j = 0; j < ncols; j++) t->cells[i * ncols + j] = c.v[j]; tv_free(c.v); } tv_free(pr.v); pinned = 0; undo(m); tv_free(rows.v); tv_free(vs.v);\n  return t;\n}\nstatic int rt_s2a_rows(Term *spec, Term *args, Term *Rows) {\n  spec = deref(spec);\n  TV as = items(args); size_t n = as.n; Term *x[16]; int nfree = 0, ok = n <= 16;\n  for (size_t j = 0; ok && j < n; j++) { x[j] = deref(as.v[j]); if (x[j]->tag == T_VAR) { for (size_t i = 0; i < j; i++) if (x[i] == x[j]) ok = 0; nfree++; } else if (!is_ground(x[j])) ok = 0; }\n  S2ATab *t = ok ? s2a_tab(spec, n) : NULL;\n  if (!t) { tv_free(as.v); return rt_s2a_rows_generic(spec, args, Rows); }\n  Term *r;\n  if ((size_t)nfree == n) r = t->all;\n  else { TV res = { 0 }; for (size_t i = 0; i < t->n; i++) { int m = 1; for (size_t j = 0; j < n && m; j++) if (x[j]->tag != T_VAR && !ground_eq(x[j], t->cells[i * n + j])) m = 0; if (m) tv_push(&res, t->rows[i]); } r = tv_list(&res); tv_free(res.v); }\n  tv_free(as.v);\n  return unify(Rows, r);\n}\n/* nondeterministic builtins as packets: every answer of the builtin, in Prolog order */\nstatic void row_of(TV *res, Term *g) { tv_push(res, mk_e(mk_cons(resolve(g), NIL))); }\nstatic int rt_builtin_rows(Term *g, Term *P) {\n  g = deref(g); TV res = { 0 }; const char *f = g->name; int n = g->arity; Term **a = g->args; size_t m = TR_TOP;\n#define TRY(cond) do { STEP(); if (cond) row_of(&res, g); undo(m); } while (0)\n  if (!strcmp(f, \"member\") && n == 2) { Term *l = deref(a[1]); while (is_cons(l)) { TRY(unify(a[0], l->args[0])); l = deref(l->args[1]); } if (l->tag == T_VAR) dl_die(\"member/2 on a partial list has no finite packet\", NULL); }\n  else if (!strcmp(f, \"between\") && n == 3) { long long lo = eval(a[0]).i; Term *hi = deref(a[1]); if (hi->tag == T_ATOM) dl_die(\"between/3 with inf has no finite packet\", NULL); long long h = eval(hi).i; Term *x = deref(a[2]);\n    if (x->tag == T_INT) { if (x->iv >= lo && x->iv <= h) row_of(&res, g); } else for (long long i = lo; i <= h; i++) TRY(unify(x, mk_int(i))); }\n  else if (!strcmp(f, \"append\") && n == 3) { TV xs = { 0 };\n    if (list_to_tv(a[0], &xs)) { Term *r = deref(a[1]); for (size_t i = xs.n; i-- > 0;) r = mk_cons(xs.v[i], r); TRY(unify(a[2], r)); }\n    else { TV zs = { 0 }; if (!list_to_tv(a[2], &zs)) dl_die(\"append/3 with neither list proper has no finite packet\", NULL);\n      for (size_t i = 0; i <= zs.n; i++) { Term *pre = NIL; for (size_t j = i; j-- > 0;) pre = mk_cons(zs.v[j], pre); Term *suf = NIL; for (size_t j = zs.n; j-- > i;) suf = mk_cons(zs.v[j], suf); TRY(unify(a[0], pre) && unify(a[1], suf)); } tv_free(zs.v); }\n    tv_free(xs.v); }\n  else if (!strcmp(f, \"select\") && n == 3) { TV xs = { 0 }; if (!list_to_tv(a[1], &xs)) dl_die(\"select/3 needs a proper list\", NULL);\n    for (size_t i = 0; i < xs.n; i++) { Term *r = NIL; for (size_t j = xs.n; j-- > 0;) if (j != i) r = mk_cons(xs.v[j], r); TRY(unify(a[0], xs.v[i]) && unify(a[2], r)); } tv_free(xs.v); }\n  else if ((!strcmp(f, \"nth0\") || !strcmp(f, \"nth1\")) && n == 3) { int base = f[3] == '1'; TV xs = { 0 }; list_to_tv(a[1], &xs); Term *i0 = deref(a[0]);\n    if (i0->tag == T_INT) { long long k = i0->iv - base; if (k >= 0 && k < (long long)xs.n) TRY(unify(a[2], xs.v[k])); }\n    else for (size_t k = 0; k < xs.n; k++) TRY(unify(i0, mk_int((long long)k + base)) && unify(a[2], xs.v[k])); tv_free(xs.v); }\n  else if (!strcmp(f, \"length\") && n == 2) { TRY(bi_length_det(a)); }\n  else if (!strcmp(f, \"last\") && n == 2) { TV xs = { 0 }; list_to_tv(a[0], &xs); if (xs.n) TRY(unify(a[1], xs.v[xs.n - 1])); tv_free(xs.v); }\n  else if (!strcmp(f, \"arg\") && n == 3) { Term *t = deref(a[1]); Term *k = deref(a[0]); if (t->tag == T_CMP) { if (k->tag == T_INT) { if (k->iv >= 1 && k->iv <= t->arity) TRY(unify(a[2], t->args[k->iv - 1])); } else for (int i = 0; i < t->arity; i++) TRY(unify(k, mk_int(i + 1)) && unify(a[2], t->args[i])); } }\n  else if (!strcmp(f, \"permutation\") && n == 2) { TV xs = { 0 }; Term *src = a[0], *oth = a[1]; if (!list_to_tv(src, &xs)) { tv_free(xs.v); xs.n = 0; src = a[1]; oth = a[0]; if (!list_to_tv(src, &xs)) dl_die(\"permutation/2 needs a proper list\", NULL); }\n    size_t k = xs.n; size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; idx[0] = 0;\n    /* iterative depth-first enumeration in Prolog's order (select/3 based permutation) */\n    TV cur = { 0 };\n    for (;;) {\n      if ((size_t)d == k) { TRY(unify(oth, tv_list(&cur))); d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n      while (idx[d] < k && used[idx[d]]) idx[d]++;\n      if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n      used[idx[d]] = 1; tv_push(&cur, xs.v[idx[d]]); d++; idx[d] = 0;\n    }\n    free(idx); free(used); tv_free(cur.v); tv_free(xs.v); }\n  else if (!strcmp(f, \"atom_concat\") && n == 3) { Term *x = deref(a[0]), *y = deref(a[1]);\n    if (x->tag != T_VAR && y->tag != T_VAR) { SB b = { 0 }; sb_puts(&b, text_of(x)); sb_puts(&b, text_of(y)); TRY(unify(a[2], mk_atom(b.s))); }\n    else { char *z = text_of(a[2]); size_t L = strlen(z); for (size_t i = 0; i <= L; i++) { if (i < L && (z[i] & 0xC0) == 0x80) continue; char *p = (char *)alloc(i + 1); memcpy(p, z, i); p[i] = 0; TRY(unify(x, mk_atom(p)) && unify(y, mk_atom(z + i))); } } }\n  else if (!strcmp(f, \"char_type\") && n == 2) { Term *b2[2] = { a[0], a[1] }; TRY(bi_call(\"code_type/2\", b2)); }\n  else dl_die(\"builtin_rows: not available in the C runtime:\", f);\n#undef TRY\n  int r = unify(P, tv_list(&res)); tv_free(res.v); return r;\n}\nstatic int rt_unsupported(const char *what) { dl_die(\"predicate was not converted:\", what); return 0; }\n\n/* ---------- top level ---------- */\n/* --events (the interpreter): each answer is printed between two \\x1e marks, so that a program's own\n   output can't be taken for an answer; --first stops after the first answer (as swipl -g Goal). */\nstatic int ev_mode = 0, first_only = 0;\nstatic void print_packet(Term *R, const char **names, int nv) {\n  TV it = items(R); size_t rows = 0;\n  for (size_t i = 0; i < it.n; i++) {\n    Term *x = deref(it.v[i]);\n    if (is_out(x)) { fputs(text_of(x->args[0]), stdout); continue; }\n    if (x->tag != T_CMP) continue;\n    if (first_only && rows) break;\n    rows++;\n    if (ev_mode) putchar('\\x1e');\n    TV vals = items(x->args[0]);\n    show_vars.n = 0;\n    if (!nv) puts(\"true\");\n    else { for (int j = 0; j < nv; j++) { char *s = show_term(vals.v[j], 1); printf(\"%s%s = %s\", j ? \", \" : \"\", names[j], s); free(s); } putchar('\\n'); }\n    tv_free(vals.v);\n    if (ev_mode) putchar('\\x1e');\n  }\n  if (!rows && !ev_mode) puts(\"false\");\n  tv_free(it.v);\n}\nstatic double now_ms(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e3 + ts.tv_nsec / 1e6; }\nstatic void rt_init(void) {\n  NIL = mk_atom(\"[]\"); A_TRUE = mk_atom(\"true\"); A_E = mk_atom(\"e\"); A_OUT = mk_atom(\"out\");\n  A_FOUND = mk_atom(\"found\"); A_NONE = mk_atom(\"none\"); A_MINUS = mk_atom(\"-\"); A_DOT = mk_atom(\".\"); A_CUT = mk_atom(\"cut\");\n}\n/* first-argument selection test */\nstatic int fa(Term *x, int tag, const char *name, int arity, long long iv) {\n  x = deref(x); if (x->tag == T_VAR) return 1;\n  if (tag < 0) return 1; /* clause head first argument is a variable */\n  if (x->tag != tag) return 0;\n  switch (tag) { case T_ATOM: return x->name == name; case T_INT: return x->iv == iv; case T_CMP: return x->name == name && x->arity == arity; default: return 1; }\n}\n/* ---------- end of runtime ---------- */\n";P.DETLOG_RUNTIME_PL="/*  detlog_runtime.pl - the Detlog runtime for SWI-Prolog, written by pl2detlog.\n\n    Load it before a converted program:   ?- [detlog_runtime], [program_detlog].\n    Run a query predicate:                 ?- '$query1__cp'(X, Rows).\n\n    The library is written in the style it supports: no cut, no ;, no ->, no \\+, no findall/3,\n    and clauses are told apart by their first argument, so first-argument indexing leaves no\n    choicepoint.  if_commit/3 is the one primitive commitment construct: it takes the first\n    answer of its condition (conditions are deterministic builtins), and runs the else branch\n    only when the condition has no answer.\n*/\n\n:- dynamic('$detlog_memo'/2).\n\nif_commit(C, T, E) :- ( call(C) -> call(T) ; call(E) ).\n\n% ---- packets: lists of e(Row), out(Text) and cut items ----\nrows_concat([], []).\nrows_concat([L|Ls], R) :- rows_concat(Ls, R0), dl_append(L, R0, R).\n\ndl_append([], L, L).\ndl_append([X|Xs], L, [X|R]) :- dl_append(Xs, L, R).\n\n% cut markers: stop after the first list that contains one\nrows_concat_cut([], []).\nrows_concat_cut([L|Ls], R) :- if_commit(dl_has_cut(L), R = L, (rows_concat_cut(Ls, R0), dl_append(L, R0, R))).\nrows_cut_concat(Ls, R) :- rows_concat_cut(Ls, R0), strip_cut(R0, R).\nstrip_cut([], []).\nstrip_cut([I|Is], R) :- dl_strip(I, Is, R).\ndl_strip(cut, Is, R) :- strip_cut(Is, R).\ndl_strip(e(X), Is, [e(X)|R]) :- strip_cut(Is, R).\ndl_strip(out(T), Is, [out(T)|R]) :- strip_cut(Is, R).\ndl_has_cut([I|Is]) :- if_commit(I == cut, true, dl_has_cut(Is)).\ncut_in(e(_), O) :- dl_has_cut(O).\n\n% splice_extend(Packet, Pattern, e(Env), Out): each answer row, unified with the call, extends Env\nsplice_extend([], _, _, []).\nsplice_extend([I|Is], Pat, Env, Out) :- dl_se(I, Pat, Env, O1), splice_extend(Is, Pat, Env, O2), dl_append(O1, O2, Out).\ndl_se(out(T), _, _, [out(T)]).\ndl_se(cut, _, _, [cut]).\ndl_se(e(R), Pat, Env, O) :- copy_term(Pat-Env, P2-E2), if_commit(P2 = R, O = [E2], O = []).\n\n% project_rows(EnvPacket, EnvVars, HeadArgs, Rows)\nproject_rows([], _, _, []).\nproject_rows([I|Is], Vs, H, Out) :- dl_pr(I, Vs, H, O1), project_rows(Is, Vs, H, O2), dl_append(O1, O2, Out).\ndl_pr(out(T), _, _, [out(T)]).\ndl_pr(cut, _, _, [cut]).\ndl_pr(e(R), Vs, H, O) :- copy_term(Vs-H, V2-H2), if_commit(V2 = R, O = [e(H2)], O = []).\n\n% project_list(Rows, e(EnvPattern), Template, Values)\nproject_list([], _, _, []).\nproject_list([I|Is], EP, T, Out) :- dl_pl(I, EP, T, O1), project_list(Is, EP, T, O2), dl_append(O1, O2, Out).\ndl_pl(out(_), _, _, []).\ndl_pl(cut, _, _, []).\ndl_pl(e(R), EP, T, O) :- copy_term(EP-T, E2-T2), if_commit(E2 = e(R), O = [T2], O = []).\n\n% packet_first(Packet, OutputBeforeFirstRow, [FirstRow] or [])\npacket_first([], [], []).\npacket_first([I|Is], Pre, F) :- dl_pf(I, Is, Pre, F).\ndl_pf(out(T), Is, [out(T)|Pre], F) :- packet_first(Is, Pre, F).\ndl_pf(cut, Is, Pre, F) :- packet_first(Is, Pre, F).\ndl_pf(e(R), _, [], [e(R)]).\n\npacket_split([], [], []).\npacket_split([I|Is], O, R) :- dl_ps(I, Is, O, R).\ndl_ps(out(T), Is, [out(T)|O], R) :- packet_split(Is, O, R).\ndl_ps(cut, Is, O, R) :- packet_split(Is, O, R).\ndl_ps(e(X), Is, O, [e(X)|R]) :- packet_split(Is, O, R).\n\n% output as data\neffect_text(G, T) :- with_output_to(string(T), G).\n\n% facts: the rows that unify with the call\ncp_filter([], _, []).\ncp_filter([e(F)|Fs], Pat, Out) :- copy_term(Pat, P2), copy_term(F, F2), if_commit(P2 = F2, Out = [e(P2)|O], Out = O), cp_filter(Fs, Pat, O).\n\naggregate_list(S, Ts, R) :- dl_agg(S, Ts, R).\ndl_agg(count, Ts, N) :- length(Ts, N).\ndl_agg(sum, Ts, S) :- dl_sum(Ts, 0, S).\ndl_agg(max, [T|Ts], M) :- X is T, dl_max(Ts, X, M).\ndl_agg(min, [T|Ts], M) :- X is T, dl_min(Ts, X, M).\ndl_agg(bag, Ts, Ts).\ndl_agg(set, Ts, S) :- sort(Ts, S).\ndl_sum([], S, S).\ndl_sum([T|Ts], A, S) :- A1 is A + T, dl_sum(Ts, A1, S).\ndl_max([], M, M).\ndl_max([T|Ts], A, M) :- X is T, if_commit(X > A, dl_max(Ts, X, M), dl_max(Ts, A, M)).\ndl_min([], M, M).\ndl_min([T|Ts], A, M) :- X is T, if_commit(X < A, dl_min(Ts, X, M), dl_min(Ts, A, M)).\n\n% independent generators: splice_safe/2 guard and the Cartesian product in Prolog order\nsplice_safe(A, B) :- term_variables(A, VA), term_variables(B, VB), dl_no_shared(VA, VB).\ndl_no_shared([], _).\ndl_no_shared([V|Vs], VB) :- if_commit(dl_var_in(VB, V), fail, dl_no_shared(Vs, VB)).\ndl_var_in([W|Ws], V) :- if_commit(V == W, true, dl_var_in(Ws, V)).\nsplice2([], _, _, _, _, []).\nsplice2([A|As], PB, PatA, PatB, Env, Out) :- dl_sp(A, PB, PatA, PatB, Env, O1), splice2(As, PB, PatA, PatB, Env, O2), dl_append(O1, O2, Out).\ndl_sp(out(T), _, _, _, _, [out(T)]).\ndl_sp(e(RA), PB, PatA, PatB, Env, Out) :- dl_sp2(PB, RA, PatA, PatB, Env, Out).\ndl_sp2([], _, _, _, _, []).\ndl_sp2([B|Bs], RA, PatA, PatB, Env, Out) :- dl_sp3(B, RA, PatA, PatB, Env, O1), dl_sp2(Bs, RA, PatA, PatB, Env, O2), dl_append(O1, O2, Out).\ndl_sp3(out(_), _, _, _, _, []).\ndl_sp3(e(RB), RA, PatA, PatB, Env, O) :- copy_term(f(PatA, PatB, Env), f(A2, B2, E2)), if_commit((A2 = RA, B2 = RB), O = [E2], O = []).\n\n% memo tables, keyed by call variant\nmemo_lookup(K, Args, Found) :-\n    copy_term(K-Args, Key), numbervars(Key, 0, _),\n    if_commit('$detlog_memo'(Key, Stored), (copy_term(Stored, f(A2, R2)), A2 = Args, Found = found(R2)), Found = none).\nmemo_store(K, Args, Rows) :-\n    copy_term(K-Args, Key), numbervars(Key, 0, _),\n    if_commit('$detlog_memo'(Key, _), true, assertz('$detlog_memo'(Key, f(Args, Rows)))).\n\n% S2A loops: row I of s2a(K, Columns) for I = 0..K-1; a bound integer on a linear column is solved directly\ns2a_rows(s2a(K, Cols), Args, Rows) :-\n    if_commit(dl_s2a_direct(Cols, Args, K, Is), true, (K1 is K - 1, dl_numlist(0, K1, Is))),\n    dl_s2a_loop(Is, Cols, Args, Rows).\ndl_s2a_direct([C|Cs], [A|As], K, Is) :- if_commit(dl_s2a_solve(C, A, K, Is0), Is = Is0, dl_s2a_direct(Cs, As, K, Is)).\ndl_s2a_solve(newton([D0, D1]), A, K, Is) :-\n    integer(A), D1 =\\= 0,\n    if_commit((0 is (A - D0) mod D1, I is (A - D0) // D1, I >= 0, I < K), Is = [I], Is = []).\ndl_numlist(L, H, Ls) :- if_commit(L > H, Ls = [], (Ls = [L|T], L1 is L + 1, dl_numlist(L1, H, T))).\ndl_s2a_loop([], _, _, []).\ndl_s2a_loop([I|Is], Cols, Args, Rows) :-\n    dl_s2a_row(Cols, I, Row), copy_term(Args, A2),\n    if_commit(A2 = Row, Rows = [e(A2)|R1], Rows = R1),\n    dl_s2a_loop(Is, Cols, Args, R1).\ndl_s2a_row([], _, []).\ndl_s2a_row([C|Cs], I, [V|Vs]) :- dl_s2a_val(C, I, V), dl_s2a_row(Cs, I, Vs).\ndl_s2a_val(const(T), _, T).\ndl_s2a_val(data(Vs), I, V) :- nth0(I, Vs, V).\ndl_s2a_val(newton(Ds), I, V) :- dl_newton(Ds, I, 0, 1, 0, V).\n% sum of D_k * C(I, k); C(I, k+1) = C(I, k) * (I - k) / (k + 1)\ndl_newton([], _, _, _, V, V).\ndl_newton([D|Ds], I, K, C, A, V) :- A1 is A + D * C, C1 is C * (I - K) // (K + 1), K1 is K + 1, dl_newton(Ds, I, K1, C1, A1, V).\n\n% nondeterministic builtins as packets: candidate instances of the goal, in Prolog order.\n% splice_extend/4 keeps the candidates that unify with the call.\nbuiltin_rows(G, P) :- functor(G, F, N), if_commit(dl_br_known(F, N), dl_br(F, G, P), dl_br_other(G, P)).\ndl_br_known(member, 2). dl_br_known(between, 3). dl_br_known(append, 3). dl_br_known(select, 3).\ndl_br_known(nth0, 3). dl_br_known(nth1, 3). dl_br_known(length, 2). dl_br_known(last, 2).\ndl_br(member, member(X, L), P) :- dl_member_rows(L, X, L, P).\ndl_br(between, between(L, H, X), P) :- if_commit(integer(X), if_commit((X >= L, X =< H), P = [e([between(L, H, X)])], P = []), (H \\== inf, H \\== infinite, dl_between_rows(L, H, L, P))).\ndl_br(append, append(A, B, C), P) :- if_commit(is_list(A), (dl_append(A, B, C2), P = [e([append(A, B, C2)])]), dl_append_rows(C, [], C, A, B, P)).\ndl_br(select, select(X, L, R), P) :- dl_select_rows(L, [], X, L, R, P).\ndl_br(nth0, nth0(I, L, E), P) :- dl_nth_rows(L, 0, nth0, I, L, E, P).\ndl_br(nth1, nth1(I, L, E), P) :- dl_nth_rows(L, 1, nth1, I, L, E, P).\ndl_br(length, length(L, N), P) :- length(L, N), P = [e([length(L, N)])].\ndl_br(last, last(L, X), P) :- if_commit(last(L, X0), P = [e([last(L, X0)])], P = []).\ndl_member_rows([], _, _, []).\ndl_member_rows([H|T], X, L, [e([member(H, L)])|P]) :- dl_member_rows(T, X, L, P).\ndl_between_rows(I, H, L0, P) :- if_commit(I > H, P = [], (P = [e([between(L0, H, I)])|P1], I1 is I + 1, dl_between_rows(I1, H, L0, P1))).\ndl_append_rows([], Pre, C, _, _, [e([append(PreR, [], C)])]) :- reverse(Pre, PreR).\ndl_append_rows([X|Xs], Pre, C, A, B, [e([append(PreR, [X|Xs], C)])|P]) :- reverse(Pre, PreR), dl_append_rows(Xs, [X|Pre], C, A, B, P).\ndl_select_rows([], _, _, _, _, []).\ndl_select_rows([X|Xs], Pre, X0, L, R0, [e([select(X, L, R)])|P]) :- reverse(Pre, PreR), dl_append(PreR, Xs, R), dl_select_rows(Xs, [X|Pre], X0, L, R0, P).\ndl_nth_rows([], _, _, _, _, _, []).\ndl_nth_rows([X|Xs], K, F, I, L, E, [e([G])|P]) :- G =.. [F, K, L, X], K1 is K + 1, dl_nth_rows(Xs, K1, F, I, L, E, P).\n% other nondeterministic builtins (sub_atom/5, permutation/2, ...) have no deterministic enumerator here\ndl_br_other(G, P) :- findall(e([G]), G, P).\n\ndetlog_unsupported(PI, Msg) :- throw(error(detlog_unsupported(PI, Msg), _)).\n\n% print a query packet the way the pl2detlog app does\ndetlog_print(Names, Rows) :- dl_print(Rows, Names).\ndl_print([], _).\ndl_print([I|Is], Ns) :- dl_print_item(I, Ns), dl_print(Is, Ns).\ndl_print_item(out(T), _) :- write(T).\ndl_print_item(cut, _).\ndl_print_item(e(Vs), Ns) :- if_commit(Ns = [], writeln(true), (dl_print_vals(Ns, Vs), nl)).\ndl_print_vals([N|Ns], [V|Vs]) :- format(\"~w = ~q\", [N, V]), dl_print_more(Ns, Vs).\ndl_print_more([], []).\ndl_print_more([N|Ns], [V|Vs]) :- format(\", ~w = ~q\", [N, V]), dl_print_more(Ns, Vs).\n";})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
