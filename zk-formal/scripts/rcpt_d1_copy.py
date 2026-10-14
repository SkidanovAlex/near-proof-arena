#!/usr/bin/env python3
"""Generate the D1 copies of the D0a receipt-view chain (lane v3-d1-phase2, item V4).

Usage (from zk-formal/, after `lake build` of the D0a modules and of the taint script):

    lake env lean --run scripts/RcptTaint.lean taint.tsv ZkFormal.NearV3.Assembly.RcptViewV3 \
        -- ZkFormal.NearV3.Assembly.rcptV3_view_nearAir
    awk -F'\t' '$3==1' taint.tsv > scripts/rcpt_d1_taint.tsv     # the committed taint set
    python3 scripts/rcpt_d1_copy.py [--check] [scripts/rcpt_d1_taint.tsv]

`--check` regenerates in memory and fails if a committed copy differs (no file is written).

Plan: docs/zk-formal/V3-D1-PHASE2.md section 7.  For every D0a module M with a tainted declaration
(`RcptTaint.lean`: its type or value depends on `TableLocal <receipt table>`), writes
`ZkFormal/NearV3/D1/R/<M below ZkFormal/NearV3>.lean`:

* the source of M with every *untainted* declaration removed (they are used from M itself,
  which the copy imports) -- the namespaces, `open`s, `variable`s and local notations stay;
* every tainted declaration `N` renamed to `N_d1` (same namespace), and every reference to a
  tainted constant (from the module's `.ilean`) renamed the same way, so name resolution in
  the copy is the original's;
* `TableLocal receiptArithmeticCandidate` / `TableLocal candidateTable` replaced by
  `TableLocal ZkFormal.NearV3.D1.RcptD1.rcptK` (`D1/R/Base.lean`);
* declarations listed in `scripts/rcpt_d1_overrides.lean` replaced by the hand-written text
  there (the deltas: `con` with the `replC' e = e` side condition, the six changed
  constraints and their consumers).

Private declarations of M that a copied declaration uses are copied verbatim (they are not
visible from another module).  The modules `EXCLUDE` (the `nearAirV3`-specific view) are
written by hand.
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB = os.path.join(ROOT, '.lake/build/lib/lean')
EXCLUDE = {'ZkFormal.NearV3.Assembly.RcptViewV3', 'ZkFormal.NearV3.Assembly.ExtractV3'}
TABLES = {'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptArithmeticCandidate',
          'ZkFormal.NearV3.Assembly.ReceiptCandidateRouting.candidateTable'}
LOCAL_K = 'ZkFormal.NearV3.D1.RcptD1.LocalD1'
SUFFIX = '_d1'
# copies whose deltas use `Delta/Body` (its imports are in their closures)
BODY_MODS = {'RcptCandidateBytesViewProof', 'RcptCandidateTableWellformed', 'RcptCandidateTableTraffic'}


def copy_mod(m):
    assert m.startswith('ZkFormal.NearV3.')
    return 'ZkFormal.NearV3.D1.R.' + m[len('ZkFormal.NearV3.'):]


def mod_path(m, ext):
    return os.path.join(ROOT if ext == '.lean' else LIB, m.replace('.', '/') + ext)


_ilean = {}


def ilean(m):
    if m not in _ilean:
        p = mod_path(m, '.ilean')
        _ilean[m] = json.load(open(p)) if os.path.exists(p) else None
    return _ilean[m]


_closure = {}


def closure(m):
    """Transitive imports of m (project modules with an .ilean), excluding m."""
    if m in _closure:
        return _closure[m]
    out = set()
    d = ilean(m)
    if d:
        for imp in d['directImports']:
            n = imp[0]
            if ilean(n) is None:
                continue
            out.add(n)
            out |= closure(n)
    _closure[m] = out
    return out


def plain(n):
    """Display name of a (possibly private) constant."""
    m = re.match(r'_private\.(.*?)\.0\.(.*)', n)
    return m.group(2) if m else n


def comps(n):
    return plain(n).split('.')


def renamed(n):
    c = comps(n)
    c[-1] = c[-1] + SUFFIX
    return '.'.join(c)


def parse_patches():
    p = os.path.join(ROOT, 'scripts/rcpt_d1_overrides.lean')
    out = {}
    if not os.path.exists(p):
        return out
    txt = open(p).read()
    for mm in re.finditer(r'-- @patch (\S+)\n<<<\n(.*?)\n===\n(.*?)\n>>>', txt, re.S):
        out.setdefault(mm.group(1), []).append((mm.group(2), mm.group(3)))
    return out


def parse_overrides():
    p = os.path.join(ROOT, 'scripts/rcpt_d1_overrides.lean')
    out = {}
    if not os.path.exists(p):
        return out
    cur = None
    buf = []
    for line in open(p).read().split('\n'):
        mm = re.match(r'-- @override (\S+)\s*$', line)
        if re.match(r'-- @patch ', line):
            if cur:
                out[cur] = '\n'.join(buf).rstrip('\n')
            cur, buf = None, []
            continue
        if mm:
            if cur:
                out[cur] = '\n'.join(buf).rstrip('\n')
            cur, buf = mm.group(1), []
        elif cur is not None:
            buf.append(line)
    if cur:
        out[cur] = '\n'.join(buf).rstrip('\n')
    return out


DECL_RE = re.compile(r'(private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
                     r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|example)\b')


def strip_mods(t):
    t = t.lstrip()
    while True:
        if t.startswith('/--'):
            t = t[t.index('-/') + 2:].lstrip()
        elif t.startswith('@['):
            t = t[t.index(']') + 1:].lstrip()
        else:
            return t


PREFIX_RE = re.compile(r'^\s*((set_option\s+\S+\s+\S+|open\s+[^\n]*|omit\s+[^\n]*|include\s+[^\n]*)\s+in)\s*$')


def main():
    args = [a for a in sys.argv[1:] if a != '--check']
    check = '--check' in sys.argv[1:]
    src_tsv = args[0] if args else os.path.join(ROOT, 'scripts/rcpt_d1_taint.tsv')
    taint = [l.rstrip('\n').split('\t') for l in open(src_tsv) if l.strip()]
    mismatches = []
    tainted = {r[0] for r in taint if r[2] == '1'}
    needed_mod = {}
    for r in taint:
        needed_mod.setdefault(r[1], set()).add(r[0])
    overrides = parse_overrides()
    patches = parse_patches()
    applied = set()
    mods = sorted({r[1] for r in taint if r[2] == '1'} - EXCLUDE)
    gen = set(mods)
    report = []
    for m in mods:
        src = open(mod_path(m, '.lean')).read().split('\n')
        d = ilean(m)
        decls = d['decls']
        keep = {n for n in decls if n in tainted}
        # private helpers used by kept declarations
        refs = d['references']
        changed = True
        while changed:
            changed = False
            for key, v in refs.items():
                k = json.loads(key)
                if 'c' not in k:
                    continue
                n = k['c']['n']
                if not n.startswith('_private.') or n in keep or n not in decls:
                    continue
                if any(len(u) > 4 and u[4] in keep for u in v['usages']):
                    keep.add(n)
                    changed = True
        # line-level edits: (line, col_start, col_end, text); deletions as line spans
        delete = []
        for n, rg in decls.items():
            if n in keep:
                continue
            sl, sc, el, ec = rg[:4]
            if not DECL_RE.match(strip_mods('\n'.join(src[sl:el + 1])[sc:])):
                continue
            # include `set_option … in` / `open … in` prefix lines
            while sl > 0 and PREFIX_RE.match(src[sl - 1]):
                sl -= 1
            delete.append((sl, sc, el, ec))
        edits = []
        for key, v in refs.items():
            k = json.loads(key)
            if 'c' not in k:
                continue
            n = k['c']['n']
            if n in tainted and n in keep and n.startswith('_private.'):
                pass
            for u in v['usages']:
                l, c0, l1, c1 = u[:4]
                if l != l1:
                    continue
                # only references inside kept declarations or on `variable` lines
                owner = u[4] if len(u) > 4 else None
                if owner is not None and owner not in keep:
                    continue
                if owner is None and not src[l].lstrip().startswith('variable'):
                    continue
                text = src[l][c0:c1]
                t = text.lstrip('@')
                at = text[:len(text) - len(t)]
                if not t or t.startswith('.') or (c0 > 0 and src[l][c0 - 1] == '.') or t.startswith('_root_'):
                    continue
                tc = t.split('.')
                nc = comps(n)
                if n in TABLES:
                    mm = re.search(r'((?:ZkFormal\.Near\.)?TableLocal)\s+$', src[l][:c0])
                    if mm:
                        edits.append((l, mm.start(1), c1, LOCAL_K))
                    continue
                if tc != nc[-len(tc):]:
                    if n in tainted:
                        report.append(f'{m}:{l+1}:{c0}: cannot rename reference {text!r} to {n}')
                    continue
                if n.startswith('_private.'):
                    continue
                # fully qualified: the copy imports more modules than the original, so a short
                # name could resolve to a later declaration of the same namespace
                if n in tainted:
                    edits.append((l, c0, c1, at + '.'.join(renamed(n).split('.')[-len(tc):])))
        # declaration names
        for n in keep:
            if n.startswith('_private.'):
                continue
            rg = decls[n]
            l, c0, l1, c1 = rg[4:8]
            text = src[l][c0:c1]
            tc = text.split('.')
            nc = comps(n)
            if tc == nc[-len(tc):]:
                edits.append((l, c0, c1, '.'.join(renamed(n).split('.')[-len(tc):])))
            else:
                report.append(f'{m}:{l+1}: cannot rename declaration {text!r} ({n})')
        # overrides: replace the whole declaration text
        ov_spans = []
        for n in keep:
            if plain(n) in overrides:
                sl, sc, el, ec = decls[n][:4]
                ov_spans.append((sl, sc, el, ec, overrides[plain(n)]))
        # apply: build the output line by line
        lines = list(src)
        # edits inside override spans are dropped
        def in_span(l, c, spans):
            for s in spans:
                if (l, c) >= (s[0], s[1]) and (l, c) < (s[2], s[3]):
                    return True
            return False
        edits = [e for e in edits if not in_span(e[0], e[1], ov_spans) and not in_span(e[0], e[1], delete)]
        # an edit contained in another one (the `TableLocal` reference inside `TableLocal T`) goes
        edits = [e for e in edits if not any(f is not e and f[0] == e[0] and f[1] <= e[1] and e[2] <= f[2]
                                           and (f[1], f[2]) != (e[1], e[2]) for f in edits)]
        edits.sort(key=lambda e: (e[0], -e[1]))
        for l, c0, c1, t in edits:
            lines[l] = lines[l][:c0] + t + lines[l][c1:]
        # spans (deletions / overrides), from the bottom; columns of the first line are
        # unaffected by reference edits on later lines, and edits on span lines were dropped
        spans = [(s[0], s[1], s[2], s[3], '') for s in delete] + ov_spans
        spans.sort(key=lambda s: (s[0], s[1]), reverse=True)
        for sl, sc, el, ec, t in spans:
            head = lines[sl][:sc]
            tail = lines[el][ec:]
            lines[sl:el + 1] = [head + t + tail]
        out = '\n'.join(lines)
        # collapse runs of blank lines
        out = re.sub(r'\n{3,}', '\n\n', out)
        # header: imports
        body_start = 0
        olines = out.split('\n')
        kept_comments = []
        while body_start < len(olines) and (olines[body_start].startswith('import ') or olines[body_start].strip() == ''
                                            or olines[body_start].startswith('--')):
            if olines[body_start].startswith('--'):
                kept_comments.append(olines[body_start])
            body_start += 1
        cl = closure(m)
        deps = sorted(g for g in gen if g in cl)
        # transitive reduction among the copies
        red = [g for g in deps if not any(g in closure(h) for h in deps if h != g)]
        imports = [f'import {m}', 'import ZkFormal.NearV3.D1.R.Delta.Constraints'] + (['import ZkFormal.NearV3.D1.R.Delta.Body'] if m.split('.')[-1] in BODY_MODS else []) + [f'import {copy_mod(g)}' for g in red]
        note = (f'/-! Generated by `scripts/rcpt_d1_copy.py` (lane v3-d1-phase2, V4): the declarations of\n'
                f'`{m}` that depend on the receipt table, re-proved for `rcptV3D1`\n'
                f'(`TableLocal ZkFormal.NearV3.D1.RcptD1.rcptK`), renamed `…{SUFFIX}`.  Do not edit by hand:\n'
                f'edit `scripts/rcpt_d1_overrides.lean` and regenerate. -/\n')
        body = '\n'.join(olines[body_start:])
        for n, pats in patches.items():
            if n in {plain(x) for x in keep}:
                for old, new in pats:
                    if old not in body:
                        report.append(f'{m}: patch for {n} does not apply: {old[:60]!r}')
                    body = body.replace(old, new, 1)
                    applied.add((n, old))
        text = '\n'.join(imports) + '\n\n' + note + '\n' + '\n'.join(kept_comments) + '\n' + body
        p = mod_path(copy_mod(m), '.lean')
        if check:
            if not os.path.exists(p) or open(p).read() != text:
                mismatches.append(p)
            continue
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w').write(text)
    # an aggregate root
    agg = '\n'.join(f'import {copy_mod(m)}' for m in mods) + '\n'
    pa = mod_path('ZkFormal.NearV3.D1.R.All', '.lean')
    if check:
        if open(pa).read() != agg:
            mismatches.append(pa)
        for x in mismatches:
            print(f'differs from the generator output: {x}')
        print('check:', 'FAIL' if mismatches else 'ok', f'({len(mods)} modules)')
        sys.exit(1 if mismatches else 0)
    open(pa, 'w').write(agg)
    for r in report:
        print(r)
    unused = set(overrides) - {plain(n) for n in tainted}
    for u in sorted(unused):
        print(f'override for an untainted / unknown declaration: {u}')
    print(f'{len(mods)} modules generated')


if __name__ == '__main__':
    main()
