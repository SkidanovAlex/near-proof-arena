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
# Profiles: `rcpt` (V4, the receipt table) and `mrk` (V5, `mrkV3` at height cap 20).
PROFILES = {
    'rcpt': dict(
        exclude={'ZkFormal.NearV3.Assembly.RcptViewV3', 'ZkFormal.NearV3.Assembly.ExtractV3'},
        # table -> (replacement, replace the `TableLocal` token too)
        tables={'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptArithmeticCandidate':
                ('ZkFormal.NearV3.D1.RcptD1.LocalD1', True),
                'ZkFormal.NearV3.Assembly.ReceiptCandidateRouting.candidateTable':
                ('ZkFormal.NearV3.D1.RcptD1.LocalD1', True)},
        suffix='_d1', dir='R', base=['ZkFormal.NearV3.D1.R.Delta.Constraints'],
        # copies whose deltas use `Delta/Body` (its imports are in their closures)
        extra={'RcptCandidateBytesViewProof': ['ZkFormal.NearV3.D1.R.Delta.Body'],
               'RcptCandidateTableWellformed': ['ZkFormal.NearV3.D1.R.Delta.Body'],
               'RcptCandidateTableTraffic': ['ZkFormal.NearV3.D1.R.Delta.Body']},
        overrides='scripts/rcpt_d1_overrides.lean', taint='scripts/rcpt_d1_taint.tsv',
        what='the receipt table, re-proved for `rcptV3D1`',
        hyp='`TableLocal receiptArithmeticCandidate` becomes `ZkFormal.NearV3.D1.RcptD1.LocalD1`'),
    'mrk': dict(
        exclude={'ZkFormal.NearV3.Assembly.LinkV3'},
        tables={'ZkFormal.NearV3.Candidates.MerkleEmpty.table': ('ZkFormal.NearV3.D1.MrkD1.tableE', False),
                'ZkFormal.NearV3.Candidates.MerklePublic.table': ('ZkFormal.NearV3.D1.MrkD1.tableP', False),
                'ZkFormal.NearV3.Candidates.MerklePublic.baseTable': ('ZkFormal.NearV3.D1.MrkD1.tableB', False)},
        suffix='_m20', dir='M', base=['ZkFormal.NearV3.D1.M.Base'], extra={},
        overrides='scripts/mrk_d1_overrides.lean', taint='scripts/mrk_d1_taint.tsv',
        what='the `mrkV3` tables, re-proved at height cap `2^20`',
        hyp='`TableLocal` of the `maxLog 19` tables becomes `ZkFormal.NearV3.D1.MrkD1.tableE/P/B`'),
    # L1 (sizing / first generation; plan V3-D1-PHASE2 §3 L1, log milestone 11): the D0a link chain
    # with the D1 statement substituted.  Untainted seed references are replaced by their D1
    # counterparts (`refs`), prior copies (V4 `_d1`, V5 `_m20`) are referenced by their copy
    # names (`prior`), and `regex` rewrites the field accesses whose structure changed.
    'link': dict(
        exclude={'ZkFormal.NearV3.Assembly.ExtractV3', 'ZkFormal.NearV3.Assembly.ExtractV3Proof',
                 'ZkFormal.NearV3.Assembly.NearAdmission', 'ZkFormal.NearV3.Assembly.RcptViewV3',
                 'ZkFormal.NearV3.Assembly.RcptViewCounts', 'ZkFormal.NearV3.Assembly.NearAirBus',
                 # the top of the chain (`GoodV3`) is redirected to `GoodD1Core` by hand
                 'ZkFormal.NearV3.Assembly.Good'},
        tables={}, suffix='_d1', dir='L',
        base=['ZkFormal.NearV3.D1.Link.Statements', 'ZkFormal.NearV3.D1.Link.Index',
              'ZkFormal.NearV3.D1.Link.PubIndex', 'ZkFormal.NearV3.D1.Link.Count', 'ZkFormal.NearV3.D1.Link.ClaimFields',
              'ZkFormal.NearV3.D1.Link.BusUsers', 'ZkFormal.NearV3.D1.Prep.Claim',
              'ZkFormal.NearV3.D1.R.All',
              'ZkFormal.NearV3.D1.M.All'],
        extra={}, overrides='scripts/link_d1_overrides.lean', taint='scripts/l1_d1_taint.tsv',
        what='the `nearAirV3` statement (`prepD0`, `preparedBytes`, `nearAirV3`, the records and the balance)',
        hyp='`prepD0 cb h = .ok p` becomes `prepD1 cb h = .ok q ∧ q.base = p` (`h : HintD1`), the tape `preparedBytes p` '
            'becomes `preparedBytesD1 q`, '
            '`nearAirV3` becomes `nearAirV3D1`, `V3RecordsWf`/`V3RecordsTraffic` become `BaseWfD1`/`BaseTrafficD1`',
        prior={'scripts/rcpt_d1_taint.tsv': '_d1', 'scripts/mrk_d1_taint.tsv': '_m20'},
        refs={'NearSpecV3.prepD0': 'ZkFormal.NearV3.D1.prepD1',
              'NearSpecV3.Hint': 'ZkFormal.NearV3.D1.HintD1',
              'ZkFormal.NearV3.Public.preparedBytes': 'ZkFormal.NearV3.D1.Public.preparedBytesD1',
              'ZkFormal.NearV3.Assembly.nearAirV3': 'ZkFormal.NearV3.D1.nearAirV3D1',
              # `D1Records.base` is D0a's record structure itself
              'ZkFormal.NearV3.Assembly.V3Records': 'ZkFormal.NearV3.Assembly.V3Records',
              'ZkFormal.NearV3.Assembly.ClaimFieldsV3': 'ZkFormal.NearV3.D1.Link.ClaimFieldsD1',
              'ZkFormal.NearV3.Assembly.busCount_nearAirV3': 'ZkFormal.NearV3.D1.Link.busCount_nearAirV3D1',
              'ZkFormal.NearV3.Assembly.UsersOk': 'ZkFormal.NearV3.D1.Link.UsersOkD1',
              'ZkFormal.NearV3.Assembly.isAt': 'ZkFormal.NearV3.D1.Link.isAtD1',
              'ZkFormal.NearV3.Assembly.V3RecordsWf': 'ZkFormal.NearV3.D1.Link.BaseWfD1',
              'ZkFormal.NearV3.Assembly.V3RecordsTraffic': 'ZkFormal.NearV3.D1.Link.BaseTrafficD1',
              'ZkFormal.NearV3.RcptV3Wf': 'ZkFormal.NearV3.D1.RcptD1.RcptV3WfD1',
              'ZkFormal.NearV3.rcptTraffic3': 'ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1',
              'ZkFormal.NearV3.Assembly.V3Balance': 'ZkFormal.NearV3.D1.Link.V3BalanceD1',
              'NearSpecV3.prepClaim': 'ZkFormal.NearV3.D1.prepClaimC',
              'ZkFormal.NearV3.Sched.prepBody_sched': 'ZkFormal.NearV3.D1.bodyD1_sched',
              'ZkFormal.NearV3.Assembly.prepBody_shape': 'ZkFormal.NearV3.D1.bodyD1_shape',
              'ZkFormal.NearV3.Assembly.RcptSkeleton.prepBody_gasPrice': 'ZkFormal.NearV3.D1.bodyD1_gasPrice',
              'ZkFormal.NearV3.Assembly.RcptSkeleton.prepBody_height': 'ZkFormal.NearV3.D1.bodyD1_height',
              'ZkFormal.NearV3.Assembly.RcptSkeleton.prepBody_outcomeRoot': 'ZkFormal.NearV3.D1.bodyD1_outcomeRoot',
              'ZkFormal.NearV3.Assembly.prepBody_routing_intervals': 'ZkFormal.NearV3.D1.bodyD1_routing_intervals',
              'ZkFormal.NearV3.Assembly.prepBody_source_owner': 'ZkFormal.NearV3.D1.bodyD1_source_owner',
              'ZkFormal.NearV3.Assembly.getElem?_node': 'ZkFormal.NearV3.D1.Link.getElem?_node_d1',
              'ZkFormal.NearV3.Assembly.getElem?_head': 'ZkFormal.NearV3.D1.Link.getElem?_head_d1',
              'ZkFormal.NearV3.Assembly.getElem?_val': 'ZkFormal.NearV3.D1.Link.getElem?_val_d1',
              'ZkFormal.NearV3.Assembly.getElem?_walk': 'ZkFormal.NearV3.D1.Link.getElem?_walk_d1',
              'ZkFormal.NearV3.Assembly.getElem?_uniq': 'ZkFormal.NearV3.D1.Link.getElem?_uniq_d1',
              'ZkFormal.NearV3.Assembly.getElem?_ups': 'ZkFormal.NearV3.D1.Link.getElem?_ups_d1',
              'ZkFormal.NearV3.Assembly.getElem?_acct': 'ZkFormal.NearV3.D1.Link.getElem?_acct_d1',
              'ZkFormal.NearV3.Assembly.getElem?_akey': 'ZkFormal.NearV3.D1.Link.getElem?_akey_d1',
              'ZkFormal.NearV3.Assembly.getElem?_bnd': 'ZkFormal.NearV3.D1.Link.getElem?_bnd_d1',
              'ZkFormal.NearV3.Assembly.getElem?_srcp': 'ZkFormal.NearV3.D1.Link.getElem?_srcp_d1',
              'ZkFormal.NearV3.Assembly.getElem?_size': 'ZkFormal.NearV3.D1.Link.getElem?_size_d1',
              'ZkFormal.NearV3.Assembly.getElem?_sort': 'ZkFormal.NearV3.D1.Link.getElem?_sort_d1',
              'ZkFormal.NearV3.Assembly.headLocal': 'ZkFormal.NearV3.D1.headLocalD1',
              'ZkFormal.NearV3.Assembly.walkLocal': 'ZkFormal.NearV3.D1.walkLocalD1',
              'ZkFormal.NearV3.Assembly.uniqLocal': 'ZkFormal.NearV3.D1.uniqLocalD1',
              'ZkFormal.NearV3.Assembly.acctLocal': 'ZkFormal.NearV3.D1.acctLocalD1',
              'ZkFormal.NearV3.Assembly.akeyLocal': 'ZkFormal.NearV3.D1.akeyLocalD1',
              'ZkFormal.NearV3.Assembly.bndLocal': 'ZkFormal.NearV3.D1.bndLocalD1',
              'ZkFormal.NearV3.Assembly.srcpLocal': 'ZkFormal.NearV3.D1.srcpLocalD1',
              'ZkFormal.NearV3.Assembly.sizeLocal': 'ZkFormal.NearV3.D1.sizeLocalD1',
              'ZkFormal.NearV3.Assembly.getElem?_rcpt': 'ZkFormal.NearV3.D1.getElem?_d1_rcpt',
              'ZkFormal.NearV3.Assembly.getElem?_mrk': 'ZkFormal.NearV3.D1.getElem?_d1_mrk',
              },
        # `p : Prep` stays (it is `q.base`); the D1 prepared statement `q` is a new implicit
        # binder after `p`, the preparation hypothesis carries `q.base = p`, the tape is `q`'s
        regex=[(r'([({]p ?: ?(?:NearSpecV3\.)?Prep[)}])(?!\s*\{q :)', r'\1 {q : ZkFormal.NearV3.D1.Public.PrepD1}'),
               # `prepBody pc h = .ok p` (the body part of `prepD0`) is `BodyD1 pc h p` (`D1/Prep/Claim`)
               (r'\bprepBody (\w+) (\w+)\s*=\s*\.ok p\b', r'ZkFormal.NearV3.D1.BodyD1 \1 \2 p'),
               (r'ZkFormal\.NearV3\.D1\.prepD1 (\w+) (\w+)\s*=\s*\.ok p\b',
                r'(ZkFormal.NearV3.D1.prepD1 \1 \2 = .ok q ∧ q.base = p)'),
               (r'ZkFormal\.NearV3\.D1\.Public\.preparedBytesD1 p\b', r'ZkFormal.NearV3.D1.Public.preparedBytesD1 q'),
               (r'\.pubSegs ?= ?(?:Public\.)?preparedSegments\b', r'.pubSegs = ZkFormal.NearV3.D1.Public.preparedSegmentsD1'),
               (r'\bZkFormal\.NearV3\.Public\.preparedSegments\.all\b', r'ZkFormal.NearV3.D1.Public.preparedSegmentsD1.all'),
               # `prepClaim cb = .ok pc` became `prepClaimC cb = .ok pc`: unfold through `prepClaimD1`
               (r'(?m)^(\s*)unfold ZkFormal\.NearV3\.D1\.prepClaimC at (\w+)\s*$',
                r'\1replace \2 := ZkFormal.NearV3.D1.prepClaimC_ok \2\n\1obtain ⟨_r, \2, rfl⟩ := \2\n'
                r'\1unfold ZkFormal.NearV3.D1.prepClaimD1 at \2'),
               # `unfold prepD0 at h; obtain ⟨pc, hc, hb⟩ := bind_ok h`: the claim and body parts
               (r'(?m)^(\s*)unfold ZkFormal\.NearV3\.D1\.prepD1 at (\w+)\s*\n\s*obtain ⟨(\w+), (\w+), (\w+)⟩ := (?:Sched\.)?bind_ok \2\s*$',
                r'\1obtain ⟨\3, \4, \5⟩ := ZkFormal.NearV3.D1.prepD1_split \2')],
        only='scripts/link_d1_only.txt', qbase=True),
}
P = PROFILES['rcpt']


def copy_mod(m):
    assert m.startswith('ZkFormal.NearV3.')
    return f"ZkFormal.NearV3.D1.{P['dir']}." + m[len('ZkFormal.NearV3.'):]


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


PRIOR = {}


def renamed(n):
    c = comps(n)
    c[-1] = c[-1] + PRIOR.get(n, P['suffix'])
    return '.'.join(c)


def parse_patches():
    p = os.path.join(ROOT, P['overrides'])
    out = {}
    if not os.path.exists(p):
        return out
    txt = open(p).read()
    for mm in re.finditer(r'-- @patch (\S+)\n<<<\n(.*?)\n===\n(.*?)\n>>>', txt, re.S):
        out.setdefault(mm.group(1), []).append((mm.group(2), mm.group(3)))
    return out


def parse_overrides():
    p = os.path.join(ROOT, P['overrides'])
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


QB = '{q : ZkFormal.NearV3.D1.Public.PrepD1}'


PREP_HYP_RE = re.compile(r'\((\w+) : \(ZkFormal\.NearV3\.D1\.prepD1 \w+ \w+ = \.ok q ∧ q\.base = p\)\)')


def decl_chunks(body):
    """Split a module body at the starts of declarations (theorem / lemma / def lines)."""
    starts = [m.start() for m in re.finditer(r'^(?:private |protected )?(?:theorem|lemma|def) \S+', body, re.M)]
    cuts = [0] + starts + [len(body)]
    return [body[a:b] for a, b in zip(cuts, cuts[1:])]


def fix_prep_bind(body):
    """`obtain ⟨pc, hc, hb⟩ := bind_ok hp` on the preparation hypothesis (D0a's `prepD0 = prepClaim
    ≫ prepBody`, used without `unfold`) becomes `prepD1_split hp`."""
    out = []
    for ch in decl_chunks(body):
        for name in PREP_HYP_RE.findall(ch):
            ch = re.sub(r'(?:ZkFormal\.NearV3\.)?(?:Sched\.)?bind_ok ' + name + r'\b', 'ZkFormal.NearV3.D1.prepD1_split ' + name, ch)
        out.append(ch)
    return ''.join(out)


DECL_START_RE = re.compile(r'(?:private |protected )?(?:theorem|lemma|def) \S+')


def sig_end(body, i):
    """End of a declaration's signature (the top-level `:` before its type), from position `i`."""
    depth = 0
    while i < len(body):
        ch = body[i]
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif ch == ':' and depth == 0 and body[i:i + 2] != ':=':
            return i
        i += 1
    return i


def drop_unused_q(body):
    """Remove the inserted `{q : PrepD1}` binder from a declaration that does not mention `q`."""
    out = []
    for ch in decl_chunks(body):
        mm = DECL_START_RE.match(ch)
        if mm and QB in ch[:sig_end(ch, mm.end())]:
            rest = ch.replace(' ' + QB, '', 1)
            if not re.search(r'(?<![.\w])q\b', rest):
                ch = rest
        out.append(ch)
    return ''.join(out)


def add_qbase(body):
    """A declaration with the `q` binder but no preparation hypothesis linking `q.base = p` gets
    the auto-params `(hq_base : q.base = p := by d1_base)` and `hq_leaves` (32-byte outcome leaves,
    `d1_leaves`) as its last binders."""
    out = []
    pos = 0
    for mm in re.finditer(r'^(?:private |protected )?(?:theorem|lemma|def) \S+', body, re.M):
        if mm.start() < pos:
            continue
        i = mm.end()
        depth = 0
        while i < len(body):
            ch = body[i]
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif ch == ':' and depth == 0 and body[i:i + 2] != ':=':
                break
            i += 1
        sig = body[mm.end():i]
        if QB in sig and 'q.base = p' not in sig:
            out.append(body[pos:i].rstrip() + ' (hq_base : q.base = p := by d1_base)\n'
                       '    (hq_leaves : ∀ l ∈ q.leaves, l.length = 32 := by d1_leaves) ')
            pos = i
    out.append(body[pos:])
    return ''.join(out)


def main():
    global P
    argv = sys.argv[1:]
    if '--profile' in argv:
        i = argv.index('--profile')
        P = PROFILES[argv[i + 1]]
        argv = argv[:i] + argv[i + 2:]
    args = [a for a in argv if a not in ('--check', '--all')]
    check = '--check' in sys.argv[1:]
    src_tsv = args[0] if args else os.path.join(ROOT, P['taint'])
    taint = [l.rstrip('\n').split('\t') for l in open(src_tsv) if l.strip()]
    mismatches = []
    subst = P.get('refs', {})

    def ref_of(n):
        # a seed constant, or a field / constructor / recursor of a seed structure
        if n in subst:
            return subst[n]
        for k, v in subst.items():
            if n.startswith(k + '.'):
                return v + n[len(k):]
        return None
    tainted = {r[0] for r in taint if r[2] == '1' and ref_of(r[0]) is None}
    renamable = set(tainted)
    for f, suf in P.get('prior', {}).items():
        for l in open(os.path.join(ROOT, f)):
            if l.strip():
                PRIOR[l.split('\t')[0]] = suf
                renamable.add(l.split('\t')[0])
    needed_mod = {}
    for r in taint:
        needed_mod.setdefault(r[1], set()).add(r[0])
    overrides = parse_overrides()
    patches = parse_patches()
    applied = set()
    mods = sorted({r[1] for r in taint if r[2] == '1'} - P['exclude'])
    if P.get('only') and '--all' not in sys.argv[1:]:
        # the finished copies (downward closed under imports); `--all` generates every module
        only = {l.strip() for l in open(os.path.join(ROOT, P['only'])) if l.strip() and not l.startswith('#')}
        mods = [m for m in mods if m in only]
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
                # (a reference after `.` is generalized field notation `x.f`: the copy `f_d1`
                # lives in the same namespace, so `x.f_d1` resolves to it)
                if not t or t.startswith('.') or t.startswith('_root_'):
                    continue
                tc = t.split('.')
                nc = comps(n)
                if n in P['tables']:
                    new, whole = P['tables'][n]
                    mm = re.search(r'((?:ZkFormal\.Near\.)?TableLocal)\s+$', src[l][:c0])
                    if mm:
                        edits.append((l, mm.start(1) if whole else c0, c1, new))
                    continue
                if ref_of(n) is not None:
                    if t.split('.') == comps(n)[-len(t.split('.')):] and len(t.split('.')) > 1 and \
                            n not in subst:
                        # `S.f` written qualified: replace the whole reference
                        edits.append((l, c0, c1, at + ref_of(n)))
                    elif n in subst:
                        edits.append((l, c0, c1, at + ref_of(n)))
                    continue
                if tc != nc[-len(tc):]:
                    if n in renamable:
                        report.append(f'{m}:{l+1}:{c0}: cannot rename reference {text!r} to {n}')
                    continue
                if n.startswith('_private.'):
                    continue
                # fully qualified: the copy imports more modules than the original, so a short
                # name could resolve to a later declaration of the same namespace
                if n in renamable:
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
        imports = ([f'import {m}'] + [f'import {x}' for x in P['base']] +
                   [f'import {x}' for x in P['extra'].get(m.split('.')[-1], [])] +
                   [f'import {copy_mod(g)}' for g in red])
        note = (f'/-! Generated by `scripts/rcpt_d1_copy.py` (lane v3-d1-phase2, V4): the declarations of\n'
                f'`{m}` that depend on {P["what"]}\n'
                f'({P["hyp"]}), renamed `…{P["suffix"]}`.  Do not edit by hand:\n'
                f'edit `{P["overrides"]}` and regenerate. -/\n')
        body = '\n'.join(olines[body_start:])
        for n, pats in patches.items():
            if n in {plain(x) for x in keep}:
                for old, new in pats:
                    if old not in body:
                        report.append(f'{m}: patch for {n} does not apply: {old[:60]!r}')
                    body = body.replace(old, new, 1)
                    applied.add((n, old))
        for pat, rep in P.get('regex', []):
            body = re.sub(pat, rep, body)
        if P.get('qbase'):
            body = fix_prep_bind(drop_unused_q(body))
            body = add_qbase(body)
        text = '\n'.join(imports) + '\n\n' + note + '\n' + '\n'.join(kept_comments) + '\n' + body
        p = mod_path(copy_mod(m), '.lean')
        if check:
            if not os.path.exists(p) or open(p).read() != text:
                mismatches.append(p)
            continue
        os.makedirs(os.path.dirname(p), exist_ok=True)
        if not os.path.exists(p) or open(p).read() != text:
            open(p, 'w').write(text)
    # an aggregate root
    agg = '\n'.join(f'import {copy_mod(m)}' for m in mods) + '\n'
    pa = mod_path(f"ZkFormal.NearV3.D1.{P['dir']}.All", '.lean')
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
