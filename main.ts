// mend: a command line tool that applies AI-written edits to a tree of text
// files. It reads a patch in one of four formats (unified diff, SEARCH/REPLACE
// blocks, V4A patches, JSON edits), finds the lines each edit names at the
// first of three matching tiers, and writes every change or none at all.
// Node 22, standard library only; run as `node main.ts [options] [PATCH]`.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

// ---- files as lines -------------------------------------------------------

interface Doc {
  lines: string[];
  br: string;
  ends: boolean;
}

function parseDoc(text: string): Doc {
  if (text === '') return { lines: [], br: '\n', ends: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const ends = text.endsWith(br);
  if (ends) parts.pop();
  return { lines: parts, br, ends };
}

function serializeDoc(d: Doc): string {
  if (d.lines.length === 0) return '';
  return d.lines.join(d.br) + (d.ends ? d.br : '');
}

const leadingWS = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};
const rtrimWS = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWS = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

function lineMatches(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rtrimWS(a) === rtrimWS(b);
  return trimWS(a) === trimWS(b);
}

interface Found {
  tier: number;
  positions: number[];
}

// First tier (0, then 1, then 2; only 0 when strict) at which O occurs at
// least once in lines, at or after `start`. Occurrences may overlap.
function findOcc(lines: string[], oldLines: string[], start: number, strict: boolean): Found | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const positions: number[] = [];
    for (let i = start; i + oldLines.length <= lines.length; i += 1) {
      let ok = true;
      for (let j = 0; j < oldLines.length; j += 1) {
        if (!lineMatches(lines[i + j]!, oldLines[j]!, tier)) { ok = false; break; }
      }
      if (ok) positions.push(i);
    }
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

// First tier at which a single line equal to `anchor` occurs at or after
// `start`, and its first position at that tier.
function findSingle(lines: string[], anchor: string, start: number, strict: boolean): { tier: number; index: number } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    for (let i = start; i < lines.length; i += 1) {
      if (lineMatches(lines[i]!, anchor, tier)) return { tier, index: i };
    }
  }
  return null;
}

// One line of the replacement text. ctx is the index into O when the line is
// a context line (written as the file's own matched line); null for a new
// line, which may be re-indented at tier 2.
interface NewItem {
  text: string;
  ctx: number | null;
}

function buildNew(oldLines: string[], items: NewItem[], fileLines: string[], pos: number, tier: number): string[] {
  if (oldLines.length === 0) return items.map((it) => it.text);
  const f = leadingWS(fileLines[pos] ?? '');
  const p = leadingWS(oldLines[0]!);
  const out: string[] = [];
  for (const it of items) {
    if (it.ctx !== null) {
      out.push(fileLines[pos + it.ctx]!);
      continue;
    }
    let t = it.text;
    if (tier === 2 && t.trim() !== '' && t.startsWith(p)) t = f + t.slice(p.length);
    out.push(t);
  }
  return out;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { old: string; next: string }[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const toLf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = toLf(before);
      const old = toLf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + toLf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- unified diffs (section 6) -------------------------------------------

interface HunkElem {
  kind: 'ctx' | 'old' | 'new';
  text: string;
  noNl: boolean;
}

interface Hunk {
  a: number;
  elems: HunkElem[];
}

interface UniSection {
  diffOld: string | null;
  diffNew: string | null;
  hasHead: boolean;
  headOld: string | null;
  headNew: string | null;
  renOld: string | null;
  renNew: string | null;
  isCreate: boolean;
  isDelete: boolean;
  hunks: Hunk[];
}

function stripAB(p: string): string {
  if (p.startsWith('a/') || p.startsWith('b/')) return p.slice(2);
  return p;
}

function headerPath(line: string): string | null {
  // line starts with '--- ' or '+++ '; text after the four characters, up
  // to the first tab, with surrounding spaces removed.
  const raw = line.slice(4).split('\t')[0]!;
  const t = raw.trim();
  if (t === '/dev/null') return null;
  return stripAB(t);
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let inHeader = false;
  let i = 0;
  const hunkRe = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;
  const startSection = (oldP: string | null, newP: string | null): void => {
    cur = { diffOld: oldP, diffNew: newP, hasHead: false, headOld: null, headNew: null, renOld: null, renNew: null, isCreate: false, isDelete: false, hunks: [] };
    sections.push(cur);
    inHeader = true;
  };
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.+?) b\/(.+)$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      startSection(m[1]!, m[2]!);
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && !inHeader) {
        // a new section without a diff --git line
        startSection(null, null);
      } else if (cur === null) {
        startSection(null, null);
      }
      // header pair
      cur!.hasHead = true;
      cur!.headOld = headerPath(line);
      cur!.headNew = headerPath(lines[i + 1]!);
      i += 2;
      continue;
    }
    if (cur === null) {
      // outside a section: prose and fences are ignored
      i += 1;
      continue;
    }
    if (inHeader) {
      if (line.startsWith('--- ')) {
        // not followed by +++ (the pair case was handled above)
        throw new Exit2(`error: parse ${i + 2}`);
      }
      if (line.startsWith('rename from ')) {
        cur.renOld = line.slice('rename from '.length).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renNew = line.slice('rename to '.length).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('new file mode')) { cur.isCreate = true; i += 1; continue; }
      if (line.startsWith('deleted file mode')) { cur.isDelete = true; i += 1; continue; }
      if (line.startsWith('@@')) {
        const m = hunkRe.exec(line);
        if (m === null) throw new Exit2(`error: parse ${i + 1}`);
        inHeader = false;
        const hunk: Hunk = { a: parseInt(m[1]!, 10), elems: [] };
        cur.hunks.push(hunk);
        i += 1;
        // hunk body
        while (i < lines.length) {
          const b = lines[i]!;
          if (b.startsWith('diff --git ')) break;
          if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
          if (b === '' || b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b.startsWith('\\')) {
            if (b.startsWith('\\')) {
              const prev = hunk.elems[hunk.elems.length - 1];
              if (prev !== undefined) prev.noNl = true;
            } else if (b === '') {
              hunk.elems.push({ kind: 'ctx', text: '', noNl: false });
            } else {
              const kind = b[0] === ' ' ? 'ctx' : b[0] === '-' ? 'old' : 'new';
              hunk.elems.push({ kind, text: b.slice(1), noNl: false });
            }
            i += 1;
            continue;
          }
          break;
        }
        // empty lines at the end of a body are not part of it
        while (hunk.elems.length > 0) {
          const last = hunk.elems[hunk.elems.length - 1]!;
          if (last.kind === 'ctx' && last.text === '' && !last.noNl) hunk.elems.pop();
          else break;
        }
        continue;
      }
      // index / old mode / new mode / similarity / dissimilarity / Index: /
      // any other header line is ignored
      i += 1;
      continue;
    }
    // after hunks started, in the same section
    if (line.startsWith('@@')) {
      const m = hunkRe.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: Hunk = { a: parseInt(m[1]!, 10), elems: [] };
      cur.hunks.push(hunk);
      i += 1;
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b === '' || b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b.startsWith('\\')) {
          if (b.startsWith('\\')) {
            const prev = hunk.elems[hunk.elems.length - 1];
            if (prev !== undefined) prev.noNl = true;
          } else if (b === '') {
            hunk.elems.push({ kind: 'ctx', text: '', noNl: false });
          } else {
            const kind = b[0] === ' ' ? 'ctx' : b[0] === '-' ? 'old' : 'new';
            hunk.elems.push({ kind, text: b.slice(1), noNl: false });
          }
          i += 1;
          continue;
        }
        break;
      }
      while (hunk.elems.length > 0) {
        const last = hunk.elems[hunk.elems.length - 1]!;
        if (last.kind === 'ctx' && last.text === '' && !last.noNl) hunk.elems.pop();
        else break;
      }
      continue;
    }
    // any other line outside a body is ignored
    i += 1;
  }
  // A hunk before any section is a parse error; the loop above never starts
  // a hunk without cur, but a leading @@ line with cur===null is ignored by
  // the "outside a section" branch, so check explicitly here is not needed:
  // the spec's case is a patch whose first @@ has no section, which the
  // loop treats as prose. Re-scan for it:
  for (let k = 0; k < lines.length; k += 1) {
    if (lines[k]!.startsWith('@@')) {
      // was it consumed as a hunk? sections hold hunks; a stray @@ before
      // the first section header is a parse error.
      let seenSection = false;
      for (let j = 0; j < k; j += 1) {
        if (lines[j]!.startsWith('diff --git ') || (lines[j]!.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ '))) seenSection = true;
      }
      if (!seenSection) throw new Exit2(`error: parse ${k + 1}`);
      break;
    }
  }
  if (sections.length === 0) return [];
  return sections.map((sec) => unifiedEdit(sec, strict));
}

function unifiedEdit(sec: UniSection, strict: boolean): Edit {
  return (tree) => {
    // ---/+++ pair names the paths first, then rename from/to, then diff --git
    const oldP = sec.hasHead ? sec.headOld : sec.renOld !== null ? sec.renOld : sec.diffOld;
    const newP = sec.hasHead ? sec.headNew : sec.renNew !== null ? sec.renNew : sec.diffNew;
    const isCreate = sec.isCreate || oldP === null;
    const isDelete = sec.isDelete || newP === null;
    // safety before anything else about either path
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    if (isCreate && !isDelete) {
      const np = newP!;
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const plus: string[] = [];
      let noNl = false;
      for (const h of sec.hunks) {
        for (const e of h.elems) {
          if (e.kind === 'new') { plus.push(e.text); noNl = e.noNl; }
        }
      }
      // ends with a line break unless a \ line follows its last + line
      const text = plus.length === 0 ? '' : plus.join('\n') + (noNl ? '' : '\n');
      tree.now.set(np, text);
      return;
    }
    if (isDelete && !isCreate) {
      const op = oldP!;
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
      return;
    }
    // change or move; both paths present here
    const op = oldP!;
    const np = newP!;
    if (tree.get(op) === null) throw new Fail('missing', op);
    const isMove = op !== np;
    if (isMove && tree.get(np) !== null) throw new Fail('exists', np);
    const doc = parseDoc(tree.get(op)!);
    let d = 0;
    for (const h of sec.hunks) {
      const oldLines: string[] = [];
      const items: NewItem[] = [];
      let ctxIdx = 0;
      for (const e of h.elems) {
        if (e.kind === 'ctx') { oldLines.push(e.text); items.push({ text: e.text, ctx: ctxIdx }); ctxIdx += 1; }
        else if (e.kind === 'old') { oldLines.push(e.text); ctxIdx += 1; }
        else { items.push({ text: e.text, ctx: null }); }
      }
      // last context or + element, for the no-newline rule
      let lastNewCtx: HunkElem | undefined;
      for (let k = h.elems.length - 1; k >= 0; k -= 1) {
        if (h.elems[k]!.kind !== 'old') { lastNewCtx = h.elems[k]; break; }
      }
      if (oldLines.length > 0) {
        const found = findOcc(doc.lines, oldLines, 0, strict);
        if (found === null) throw new Fail('no-match', op);
        const want = h.a - 1 + d;
        let best = found.positions[0]!;
        let bestDist = Math.abs(best - want);
        for (const pos of found.positions) {
          const dist = Math.abs(pos - want);
          if (dist < bestDist) { best = pos; bestDist = dist; }
        }
        const touchesEnd = best + oldLines.length === doc.lines.length;
        const built = buildNew(oldLines, items, doc.lines, best, found.tier);
        doc.lines.splice(best, oldLines.length, ...built);
        if (touchesEnd) doc.ends = !(lastNewCtx !== undefined && lastNewCtx.noNl);
        d += items.length - oldLines.length;
      } else {
        const at = Math.min(h.a + d, doc.lines.length);
        const atEnd = at === doc.lines.length;
        const built = items.map((it) => it.text);
        doc.lines.splice(at, 0, ...built);
        if (atEnd) doc.ends = !(lastNewCtx !== undefined && lastNewCtx.noNl);
        d += items.length;
      }
    }
    const text = serializeDoc(doc);
    if (isMove) {
      tree.now.set(op, null);
      tree.now.set(np, text);
      tree.moves.push({ old: op, next: np });
    } else {
      tree.now.set(op, text);
    }
  };
}

// ---- SEARCH/REPLACE blocks (section 7) ------------------------------------

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') { i += 1; continue; }
    const searchLine = i + 1;
    // path: nearest line before SEARCH, after the previous block, that is
    // not blank and does not start with three backticks
    let path: string | null = null;
    for (let k = i - 1; k > prevEnd; k -= 1) {
      const t = lines[k]!;
      if (blank(t)) continue;
      if (t.trim().startsWith('```')) continue;
      path = t.trim();
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${searchLine}`);
    let sep = -1;
    let end = -1;
    for (let k = i + 1; k < lines.length; k += 1) {
      if (lines[k]!.trimEnd() === '=======') { sep = k; break; }
    }
    if (sep >= 0) {
      for (let k = sep + 1; k < lines.length; k += 1) {
        if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') { end = k; break; }
      }
    }
    if (sep < 0 || end < 0) throw new Exit2(`error: parse ${searchLine}`);
    const oldLines = lines.slice(i + 1, sep);
    const newLines = lines.slice(sep + 1, end);
    const p = path;
    edits.push((tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (oldLines.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
        return;
      }
      const cur = tree.get(p);
      if (cur === null) throw new Fail('missing', p);
      const doc = parseDoc(cur);
      const found = findOcc(doc.lines, oldLines, 0, strict);
      if (found === null) throw new Fail('no-match', p);
      if (found.positions.length > 1) throw new Fail('ambiguous', p);
      const pos = found.positions[0]!;
      const items: NewItem[] = newLines.map((t) => ({ text: t, ctx: null }));
      const built = buildNew(oldLines, items, doc.lines, pos, found.tier);
      doc.lines.splice(pos, oldLines.length, ...built);
      tree.now.set(p, serializeDoc(doc));
    });
    prevPath = p;
    prevEnd = end;
    i = end + 1;
  }
  return edits;
}

// ---- V4A patches (section 8) ----------------------------------------------

interface V4Chunk {
  anchor: string | null;
  elems: HunkElem[];
  eof: boolean;
}

interface V4Section {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  addLines: string[];
  chunks: V4Chunk[];
  lineNo: number;
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) { last = k; break; }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  const isHeader = (l: string): boolean => l.startsWith('*** Add File:') || l.startsWith('*** Delete File:') || l.startsWith('*** Update File:');
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) { i += 1; continue; }
    if (!isHeader(line)) throw new Exit2(`error: parse ${i + 1}`);
    const lineNo = i + 1;
    let kind: 'add' | 'delete' | 'update';
    if (line.startsWith('*** Add File:')) kind = 'add';
    else if (line.startsWith('*** Delete File:')) kind = 'delete';
    else kind = 'update';
    const path = line.slice(line.indexOf(':') + 1).trim();
    // collect this section's raw lines (until the next header or End Patch)
    const raw: number[] = [];
    i += 1;
    while (i < last && !isHeader(lines[i]!)) { raw.push(i); i += 1; }
    // blank lines at the end of a section are not part of it (a line
    // holding only whitespace is blank, even a lone ' ' context line)
    while (raw.length > 0 && blank(lines[raw[raw.length - 1]!]!)) raw.pop();
    const sec: V4Section = { kind, path, moveTo: null, addLines: [], chunks: [], lineNo };
    if (kind === 'add') {
      for (const idx of raw) {
        const l = lines[idx]!;
        if (l.startsWith('+')) sec.addLines.push(l.slice(1));
        else if (l === '') sec.addLines.push('');
        else throw new Exit2(`error: parse ${idx + 1}`);
      }
    } else if (kind === 'delete') {
      for (const idx of raw) {
        if (lines[idx]!.trim() !== '') throw new Exit2(`error: parse ${idx + 1}`);
      }
    } else {
      // update: optional Move to as the first line, then chunks
      let start = 0;
      // skip leading blank lines for the Move-to check
      while (start < raw.length && lines[raw[start]!] === '') start += 1;
      if (start < raw.length && lines[raw[start]!]!.startsWith('*** Move to:')) {
        sec.moveTo = lines[raw[start]!]!.slice('*** Move to:'.length).trim();
        start += 1;
      }
      let chunk: V4Chunk | null = null;
      const closeChunk = (): void => { if (chunk !== null) { sec.chunks.push(chunk); chunk = null; } };
      for (let r = start; r < raw.length; r += 1) {
        const idx = raw[r]!;
        const l = lines[idx]!;
        if (l.startsWith('@@')) {
          closeChunk();
          chunk = { anchor: l.slice(2).trim() === '' ? null : l.slice(2).trim(), elems: [], eof: false };
          continue;
        }
        if (l === '*** End of File') {
          if (chunk === null) throw new Exit2(`error: parse ${idx + 1}`);
          chunk.eof = true;
          closeChunk();
          continue;
        }
        if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
          if (chunk === null) chunk = { anchor: null, elems: [], eof: false };
          if (l === '') chunk.elems.push({ kind: 'ctx', text: '', noNl: false });
          else {
            const kind2 = l[0] === ' ' ? 'ctx' : l[0] === '-' ? 'old' : 'new';
            chunk.elems.push({ kind: kind2, text: l.slice(1), noNl: false });
          }
          continue;
        }
        throw new Exit2(`error: parse ${idx + 1}`);
      }
      closeChunk();
      if (sec.chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${lineNo}`);
    }
    edits.push(v4aEdit(sec, strict));
  }
  return edits;
}

function v4aEdit(sec: V4Section, strict: boolean): Edit {
  return (tree) => {
    const p = sec.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (sec.moveTo !== null && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
    if (sec.kind === 'add') {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, sec.addLines.length === 0 ? '' : sec.addLines.join('\n') + '\n');
      return;
    }
    if (sec.kind === 'delete') {
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    const cur = tree.get(p);
    if (cur === null) throw new Fail('missing', p);
    if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    const doc = parseDoc(cur);
    let cursor = 0;
    for (const chunk of sec.chunks) {
      if (chunk.anchor !== null) {
        const hit = findSingle(doc.lines, chunk.anchor, cursor, strict);
        if (hit === null) throw new Fail('no-match', p);
        cursor = hit.index + 1;
      }
      const oldLines: string[] = [];
      const items: NewItem[] = [];
      let ctxIdx = 0;
      for (const e of chunk.elems) {
        if (e.kind === 'ctx') { oldLines.push(e.text); items.push({ text: e.text, ctx: ctxIdx }); ctxIdx += 1; }
        else if (e.kind === 'old') { oldLines.push(e.text); ctxIdx += 1; }
        else { items.push({ text: e.text, ctx: null }); }
      }
      if (oldLines.length > 0) {
        const found = findOcc(doc.lines, oldLines, cursor, strict);
        if (found === null) throw new Fail('no-match', p);
        let pos: number | null = null;
        for (const cand of found.positions) {
          if (chunk.eof && cand + oldLines.length !== doc.lines.length) continue;
          pos = cand;
          break;
        }
        if (pos === null) throw new Fail('no-match', p);
        const built = buildNew(oldLines, items, doc.lines, pos, found.tier);
        doc.lines.splice(pos, oldLines.length, ...built);
        cursor = pos + built.length;
      } else {
        const at = chunk.eof ? doc.lines.length : cursor;
        const built = items.map((it) => it.text);
        doc.lines.splice(at, 0, ...built);
        cursor = at + built.length;
      }
    }
    const text = serializeDoc(doc);
    if (sec.moveTo !== null) {
      tree.now.set(p, null);
      tree.now.set(sec.moveTo, text);
      tree.moves.push({ old: p, next: sec.moveTo });
    } else {
      tree.now.set(p, text);
    }
  };
}

// ---- main run (sections 1, 2, 10) ------------------------------------------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const beforeMoves = [...tree.moves];
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = 0;
      for (const m of beforeMoves) tree.moves.push(m);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // rows for changed paths, with R replacing a move's D and A, sorted by
  // the path (by <new> for a move)
  interface Row { key: string; line: string }
  const rows: Row[] = [];
  const deleted = new Set<string>();
  const added = new Set<string>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (was !== null && now === null) deleted.add(p);
    else if (was === null && now !== null) added.add(p);
    else rows.push({ key: p, line: `M ${p}` });
  }
  const usedOld = new Set<string>();
  const usedNew = new Set<string>();
  for (const m of tree.moves) {
    if (tree.original(m.old) === null) continue;
    if (tree.get(m.old) !== null) continue;
    if (tree.original(m.next) !== null) continue;
    if (tree.get(m.next) === null) continue;
    if (!deleted.has(m.old) || !added.has(m.next)) continue;
    rows.push({ key: m.next, line: `R ${m.old} -> ${m.next}` });
    usedOld.add(m.old);
    usedNew.add(m.next);
  }
  for (const p of deleted) if (!usedOld.has(p)) rows.push({ key: p, line: `D ${p}` });
  for (const p of added) if (!usedNew.has(p)) rows.push({ key: p, line: `A ${p}` });
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out = [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`];
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
