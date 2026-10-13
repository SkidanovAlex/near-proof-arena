# shellcheck shell=bash
# run-v2.d/digest.sh — full-bundle balance of the SHA buses BYTES 0 and DIGEST 1 (sourced by
# run-v2.sh / run-v2-section.sh digest; in scope: here src out npudr fx HEAVY pass bad).
#
# Why (lane v3-prover-digest, 2026-10-13): the schedqv lane, assembling the 25 tables from the
# per-table CLIs, saw bus 1 report `MRK(root)` received with a ZERO digest on every fixture with
# outcomes, while `v3prove --check-only` balanced.  Cause: `npudr v3bus` evaluated the AIR with
# all-zero public inputs; table 23's root row receives `DIGEST(rootId, rootLen, pub[146..178])`
# (`p 146..177`, the outcome root of the prepared tape; Lean `mrkAcc : TableRenderV3 A.pub 23`
# with `A.pub = pubOf (preparedBytes …)`).  `v3bus` now takes the publics from the tape, as
# `v3prove` and the verifier do.  This section keeps both assemblies honest:
#
# Per fixture (public-d0a/d0 and fixtures-extra/d0; DIGEST_FX / DIGEST_MAX restrict):
#   1. `npudr v3prove --check-only`: all constraints + all buses; report.json buses 0 and 1
#      balanced; its prepared tape == `v3prepare` + `v3public`;
#   2. the per-table assembly: `v3trie` (7 tables), `v3sched`, `v3rcptfam`, `v3sha` (collector
#      bins, its bus check passes); `npudr v3bus <tape> 0,1` over ALL 25 tables balances;
#   3. fixtures with outcomes (mrk n > 0), against Lean: `np-lean-rcptfam-v3` mrk (n, levels) ==
#      Rust; `np-lean-shabins-v3` bins b0/b1 == the Rust bins; the tape's root bytes
#      [146, 178) == the top level digest of the Lean `mrkLevels` and the digest of the Lean
#      bins' job that sends it; bus 0,1 with the Lean bins in place of the Rust bins balance;
#   4. negatives (first DIGEST_NEG = 3 fixtures with a hashed outcome node): a flipped root byte
#      of the tape, a flipped child digest byte of the mrk root node, the MRK root job dropped
#      from the bins — each must unbalance bus 1.  And zero publics (the old `v3bus`) must not
#      balance (tape bytes 146..178 zeroed).
# Lean dumps are cached in $out/digest/<case>.lean* (DIGEST_FRESH=1 to recompute).
dg="$out/digest"; mkdir -p "$dg"
lrf="$here/.lake/build/bin/np-lean-rcptfam-v3"
lsb="$here/.lake/build/bin/np-lean-shabins-v3"
air="$out/nearAirV3.json"
ALLT="sha_t sha_r node head val walk uniq ups chacha rng shuf codec scandist proc mem cmp rcpt acct akey bnd srcp qv size mrk sort"
# dbus <entries dir> <tape> <out> [<table>=<file> overrides]: bus 0,1 over all 25 tables
dbus() {
  local e=$1 tp=$2 o=$3; shift 3
  local args=() t f
  for t in $ALLT; do
    f="$e/$t.json"
    for ov in "$@"; do [ "${ov%%=*}" = "$t" ] && f="${ov#*=}"; done
    args+=("$t=$f")
  done
  $HEAVY "$npudr" v3bus "$air" "$tp" 0,1 "${args[@]}" > "$o" 2>&1
}
echo "== digest: BYTES 0 / DIGEST 1 over all 25 tables (v3prove vs per-table assembly vs Lean)"
ncase=0; nprove=0; nasm=0; nout=0; nlean=0; nneg=0; negdone=0
for dir in ${DIGEST_FX:-$fx $here/fixtures-extra/d0}; do
  for case in $(ls "$dir" | head -"${DIGEST_MAX:-1000}"); do
    d="$dir/$case"; [ -f "$d/witness.bin" ] || continue
    p="$dg/$case"; e="$p.e"; rm -rf "$e" "$p.cp" "$p.neg"; mkdir -p "$e"
    ncase=$((ncase + 1))
    # 1. v3prove --check-only
    if $HEAVY "$npudr" v3prove "$d" "$p.cp" --air "$air" --check-only > "$p.cp.log" 2>&1 \
       && python3 - "$p.cp/report.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1])); b = {x['bus']: x for x in r['buses']}
sys.exit(0 if all(b[i]['nbad'] == 0 and b[i]['sent'] == b[i]['recv'] for i in (0, 1)) else 1)
PY
    then nprove=$((nprove + 1)); else bad "$case: v3prove --check-only: $(tail -1 "$p.cp.log")"; fi
    # 2. per-table assembly
    ok=1
    for t in node val head walk uniq ups size; do "$npudr" v3trie "$d" $t > "$e/$t.json" 2>/dev/null || { ok=0; bad "$case: v3trie $t"; }; done
    "$npudr" v3sched "$d" "$e" > /dev/null 2>&1 || { ok=0; bad "$case: v3sched"; }
    mo=$("$npudr" v3rcptfam "$d/claim.bin" "$d/witness.bin" "$e" --no-prefix 2>&1) || { ok=0; bad "$case: v3rcptfam"; }
    "$npudr" v3prepare "$d/claim.bin" "$d/witness.bin" "$p.prep" > /dev/null 2>&1 \
      && "$npudr" v3public "$p.prep/prep.json" "$p.tape" > /dev/null 2>&1 || { ok=0; bad "$case: no public tape"; }
    cmp -s "$p.tape" "$p.cp/prepared.bin" || { ok=0; bad "$case: v3public tape != v3prove prepared.bin"; }
    "$npudr" v3sha "$e" "$e/sha_t.json" "$e/sha_r.json" > /dev/null 2> "$p.sha.err" || { ok=0; bad "$case: v3sha: $(tail -1 "$p.sha.err")"; }
    [ $ok = 1 ] || continue
    if dbus "$e" "$p.tape" "$p.bus"; then nasm=$((nasm + 1))
    else bad "$case: per-table assembly: $(grep -E 'FAIL|IMBALANCE' "$p.bus" | head -2 | tr '\n' ' ' | cut -c1-240)"; continue; fi
    n=$(echo "$mo" | grep -o 'mrk n=[0-9]*' | cut -d= -f2)
    [ "${n:-0}" -gt 0 ] || continue
    nout=$((nout + 1))
    # 3. against Lean
    if [ "${DIGEST_FRESH:-0}" = 1 ] || [ ! -s "$p.lean/mrk.json" ]; then
      rm -rf "$p.lean"; $HEAVY "$lrf" "$d" "$p.lean" > "$p.lean.log" 2>&1 || { bad "$case: np-lean-rcptfam-v3 failed"; continue; }
    fi
    if [ "${DIGEST_FRESH:-0}" = 1 ] || [ ! -s "$p.lean.sb.json" ]; then
      $HEAVY "$lsb" "$d" > "$p.lean.sb.json" 2> "$p.lean.sb.err" || { bad "$case: np-lean-shabins-v3 failed"; continue; }
    fi
    if r=$(python3 - "$p.lean" "$p.lean.sb.json" "$e" "$p.tape" <<'PY'
import json, sys, hashlib
L, SB, R, T = sys.argv[1:5]
ld = lambda f: json.load(open(f))
lm, rm, sb = ld(L + '/mrk.json'), ld(R + '/mrk.json'), ld(SB)
bad = []
if (lm['n'], lm['levels']) != (rm['n'], rm.get('levels', [])): bad.append('mrk (n, levels) Lean != Rust')
if sb['b0'] != ld(R + '/sha_t.json') or sb['b1'] != ld(R + '/sha_r.json'): bad.append('bins Lean != Rust')
top = lm['levels'][-1][0]
root = list(open(T, 'rb').read()[146:178])
if top['dig'] != root: bad.append('tape root != Lean mrkLevels top digest')
if (rm['rootId'], rm['rootLen']) != (top['id'], top['len']): bad.append('Rust root ref != Lean top')
js = [j for b in ('b0', 'b1') for j in sb[b] if j['id'] == top['id'] and j['dmult']]
if not any(len(j['bytes']) == top['len'] and list(hashlib.sha256(bytes(j['bytes'])).digest()) == root for j in js):
    bad.append('no Lean bin job sends DIGEST(root)')
json.dump(sb['b0'], open(R + '/lean.sha_t.json', 'w')); json.dump(sb['b1'], open(R + '/lean.sha_r.json', 'w'))
print('; '.join(bad)); sys.exit(1 if bad else 0)
PY
    ) && dbus "$e" "$p.tape" "$p.lbus" sha_t="$e/lean.sha_t.json" sha_r="$e/lean.sha_r.json"; then
      nlean=$((nlean + 1))
    else bad "$case: Lean: ${r:-bus 0/1 with the Lean bins: $(grep FAIL "$p.lbus" | tr '\n' ' ')}"; fi
    # 4. negatives
    [ "$n" -ge 2 ] && [ $negdone -lt "${DIGEST_NEG:-3}" ] || continue
    negdone=$((negdone + 1)); mkdir -p "$p.neg"
    python3 - "$e" "$p.tape" "$p.neg" <<'PY'
import json, sys
R, T, N = sys.argv[1:4]
t = bytearray(open(T, 'rb').read())
x = bytearray(t); x[146] ^= 1; open(N + '/root.tape', 'wb').write(bytes(x))
x = bytearray(t); x[146:178] = bytes(32); open(N + '/zero.tape', 'wb').write(bytes(x))
m = json.load(open(R + '/mrk.json'))
h = [nd for nd in m['nodes'] if 'hashed' in nd][-1]  # the root (last hashed node, top level)
h['hashed']['l'][0] ^= 1; json.dump(m, open(N + '/mrk.json', 'w'))
rid = m['rootId']
for b in ('sha_t', 'sha_r'):
    js = json.load(open(R + '/' + b + '.json'))
    json.dump([j for j in js if j['id'] != rid], open(N + '/' + b + '.json', 'w'))
PY
    nk=0
    for k in root zero; do
      if dbus "$e" "$p.neg/$k.tape" "$p.neg/$k.out"; then bad "$case neg $k tape: bus 0/1 still balanced"
      elif grep -q "FAIL bus 1" "$p.neg/$k.out"; then nk=$((nk + 1)); else bad "$case neg $k: bus 1 not the failing bus"; fi
    done
    if dbus "$e" "$p.tape" "$p.neg/mrk.out" mrk="$p.neg/mrk.json"; then bad "$case neg mrk child digest: still balanced"
    elif grep -q "FAIL bus 1" "$p.neg/mrk.out"; then nk=$((nk + 1)); else bad "$case neg mrk: bus 1 balanced"; fi
    if dbus "$e" "$p.tape" "$p.neg/job.out" sha_t="$p.neg/sha_t.json" sha_r="$p.neg/sha_r.json"; then bad "$case neg MRK root job dropped: still balanced"
    elif grep -q "FAIL bus 1" "$p.neg/job.out"; then nk=$((nk + 1)); else bad "$case neg job: bus 1 balanced"; fi
    [ $nk = 4 ] && nneg=$((nneg + 1)) && pass "$case negatives: root tape byte / zero publics / mrk child digest / MRK root job dropped -> bus 1 unbalanced"
  done
done
[ $ncase -gt 0 ] && [ $nprove = $ncase ] && pass "digest: v3prove --check-only, buses 0 and 1 balanced on $nprove/$ncase fixtures"
[ $ncase -gt 0 ] && [ $nasm = $ncase ] && pass "digest: per-table assembly (v3trie/v3sched/v3rcptfam/v3sha) + v3bus 0,1 over all 25 tables balanced on $nasm/$ncase"
[ $nout -gt 0 ] && [ $nlean = $nout ] && pass "digest: $nlean/$nout fixtures with outcomes: Lean mrk levels/bins == Rust, tape root == Lean root digest, buses 0,1 balanced with the Lean bins"
[ $negdone -gt 0 ] && [ $nneg = $negdone ] && pass "digest: negatives on $nneg fixtures"
