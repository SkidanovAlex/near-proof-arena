#!/usr/bin/env bash
# Differential conformance for np-udr-stark-v2 (FORMATS.md §8): the Rust prover
# (../source) vs the deployed Lean v2 verifier model
# `ZkFormal.V2.verifierP Fp Fp8 AP (ZkFormal.V2.G.pg g)` (np-lean-verify-v2).
#
#   ./run-v2.sh [log ...]      (default logs: 4 6 10)
#
# 1. nearAirV3: `np-lean-export-v3` (the frozen assembled v3 AIR) is read by the
#    Rust prover, re-exported byte-identically, validated, and its per-table
#    layout (width, aux, degree, quot, send/recv groups, maxLog) at auxGroup
#    1, 2, 3 equals Lean's (`ZkFormal.Stark.Protocol`).
# 2. v2 toy (`toy::pubseg_air`, two public segments incl. prefix/indexBase/
#    startAt; layouts differ at g = 1, 2, 3): for each g and log, the Lean
#    verifier accepts the honest Rust proof (and its AIR re-exports
#    byte-identically), rejects it under every other auxGroup, rejects proof
#    mutations, and rejects mutated claims (payload byte, count, offset).
# 3. nearAirV3 per-table honest traces (src/v3): for each table with a Lean
#    aligned generator (Render/Padded.lean, Render/PaddedTrie.lean, and the
#    receipt-side Render/AcctRender.lean + Render/SizeRender.lean), seeded
#    random honest entries (`npudr v3sample`) are rendered by `npudr v3render`
#    and `np-lean-render-v3`; the dumps must be byte-identical and the trace
#    must satisfy every constraint of its nearAirV3 table (`npudr v3check`).
#    Entries that break the honest-input predicate must fail the check.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
src="$here/../source"
out="$here/out-v2"
if [ -z "${HEAVY+x}" ]; then
  if [ -x /data/illia/nearproof-deps/bin/heavy ]; then HEAVY=/data/illia/nearproof-deps/bin/heavy; else HEAVY=; fi
fi
export PATH="$HOME/.elan/bin:$PATH"
logs=("$@"); [ ${#logs[@]} -eq 0 ] && logs=(4 6 10)

fail=0
pass() { echo "PASS  $*"; }
bad()  { echo "FAIL  $*"; fail=1; }

echo "== build"
(cd "$src" && $HEAVY cargo build --release -q) || { echo "cargo build failed"; exit 2; }
(cd "$here" && $HEAVY lake build -q np-lean-verify-v2 np-lean-export-v3 np-lean-render-v3 np-lean-entries-v3 np-lean-prep-v3) || { echo "lake build failed"; exit 2; }
npudr="${CARGO_TARGET_DIR:-$src/target}/release/npudr"
lv="$here/.lake/build/bin/np-lean-verify-v2"
le="$here/.lake/build/bin/np-lean-export-v3"
rm -rf "$out"; mkdir -p "$out"

echo "== nearAirV3 (np-air-v2): Rust import vs Lean"
"$le" > "$out/nearAirV3.json"
echo "nearAirV3.json: $(stat -c %s "$out/nearAirV3.json") B sha256 $(sha256sum "$out/nearAirV3.json" | cut -c1-64)"
for g in 1 2 3; do
  if cmp -s <("$le" --layout $g) <("$npudr" layout "$out/nearAirV3.json" $g); then pass "nearAirV3 layout g=$g identical"
  else bad "nearAirV3 layout g=$g differs"; diff <("$le" --layout $g) <("$npudr" layout "$out/nearAirV3.json" $g) | head; fi
done

mutate() { # mutate <in> <out> <op> <offset> [value]
  python3 - "$@" <<'PY'
import sys
src, dst, op, off = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
b = bytearray(open(src, 'rb').read())
if op == 'flip': b[off % len(b)] ^= 0x01
elif op == 'trunc': b = b[:-1]
elif op == 'append': b += b'\x00'
elif op == 'u32': b[off:off + 4] = int(sys.argv[5]).to_bytes(4, 'little')
open(dst, 'wb').write(bytes(b))
PY
}

# verify <g> <dir> <proof> [claim] -> prints accept/reject, returns exit code
verify() {
  local g=$1 d=$2 pf=$3 cb=${4:-$2/claim.bin}
  HEAVY_MEM=${VERIFY_MEM:-4G} $HEAVY "$lv" $g "$d/air.json" "$d/pub.bin" "$cb" "$pf" 2>"$d/verify.err"
}
expect() { # expect <want> <label> <g> <dir> <proof> [claim]
  local want=$1 x=$2; shift 2
  r=$(verify "$@"); rc=$?
  if [ "$r" = "$want" ]; then pass "$x $want"; else bad "$x -> '$r' rc=$rc (want $want)"; cat "$2/verify.err"; fi
}

echo "== v2 toy proofs: Rust prover vs Lean verifierP (pg g)"
for g in 1 2 3; do
  for lg in "${logs[@]}"; do
    x="pubseg g=$g log=$lg"; d="$out/pubseg$g-$lg"; mkdir -p "$d"
    if ! $HEAVY "$npudr" toy pubseg$g $lg "$d" >/dev/null 2>&1; then bad "$x: npudr toy failed"; continue; fi
    n=$(stat -c %s "$d/proof.bin")
    expect accept "$x honest ($n B)" $g "$d" "$d/proof.bin"
    grep -q 'byte-identical=true' "$d/verify.err" && pass "$x AIR re-export byte-identical" || bad "$x AIR re-export not byte-identical"
    for h in 1 2 3; do [ $h = $g ] || expect reject "$x under auxGroup $h" $h "$d" "$d/proof.bin"; done
    for off in 0 9 40 $((n/3)) $((n/2)) $((n-40)) $((n-1)); do
      mutate "$d/proof.bin" "$d/mut.bin" flip $off; expect reject "$x proof flip@$off" $g "$d" "$d/mut.bin"
    done
    for op in trunc append; do mutate "$d/proof.bin" "$d/mut.bin" $op 0; expect reject "$x proof $op" $g "$d" "$d/mut.bin"; done
    c=$(stat -c %s "$d/claim.bin")
    mutate "$d/claim.bin" "$d/claim.mut" flip 13;          expect reject "$x seg0 payload byte" $g "$d" "$d/proof.bin" "$d/claim.mut"
    mutate "$d/claim.bin" "$d/claim.mut" flip $((c - 1));  expect reject "$x seg1 payload byte" $g "$d" "$d/proof.bin" "$d/claim.mut"
    mutate "$d/claim.bin" "$d/claim.mut" u32 0 100000;     expect reject "$x seg0 count past claim" $g "$d" "$d/proof.bin" "$d/claim.mut"
    mutate "$d/claim.bin" "$d/claim.mut" u32 8 4294967295; expect reject "$x seg1 count 2^32-1" $g "$d" "$d/proof.bin" "$d/claim.mut"
    mutate "$d/claim.bin" "$d/claim.mut" u32 4 $c;         expect reject "$x seg1 offset past claim" $g "$d" "$d/proof.bin" "$d/claim.mut"
  done
done

echo "== nearAirV3 honest per-table traces: Rust (npudr v3render) vs Lean (np-lean-render-v3)"
lr="$here/.lake/build/bin/np-lean-render-v3"
rd="$out/render"; mkdir -p "$rd"
for t in ${RENDER_TABLES:-bnd akey head val uniq walk node acct size srcp qv}; do
  for seed in 1 2 3; do
    for n in ${RENDER_SIZES:-0 1 5 37}; do
      f="$rd/$t-$seed-$n"
      "$npudr" v3sample $t $seed $n > "$f.json"
      $HEAVY "$lr" $t "$f.json" "$f.lean.bin" 2>"$f.err" || { bad "$t seed=$seed n=$n: np-lean-render-v3 failed"; continue; }
      "$npudr" v3render $t "$f.json" "$f.rust.bin" || { bad "$t seed=$seed n=$n: npudr v3render failed"; continue; }
      if cmp -s "$f.lean.bin" "$f.rust.bin"; then pass "$t seed=$seed n=$n trace identical ($(stat -c %s "$f.rust.bin") B)"
      else bad "$t seed=$seed n=$n trace differs"; fi
      # `v3check` needs honest (`*Ok`) entries; node entries come from the witness
      # (part 2c), so its random sampler only exercises the renderer identity.
      if [ "$t" = node ]; then continue; fi
      if "$npudr" v3check "$out/nearAirV3.json" $t "$f.json" >"$f.check"; then pass "$t seed=$seed n=$n $(cut -c5- "$f.check")"
      else bad "$t seed=$seed n=$n constraints fail"; head -3 "$f.check"; fi
    done
  done
done
# entries outside the honest-input predicate: the rendered trace must violate a constraint
broken() { # broken <table> <label> <python edit of list `es`>
  local t=$1 x=$2 f="$rd/broken-$1"
  "$npudr" v3sample $t 7 5 | python3 -c "import json,sys; es=json.load(sys.stdin); $3; print(json.dumps(es))" > "$f.json"
  if "$npudr" v3check "$out/nearAirV3.json" $t "$f.json" >"$f.check"; then bad "$t $x: constraints still hold"
  else pass "$t $x: constraint violated"; fi
}
broken val "non-consecutive ids" "es[2]['vid'] += 1"
broken akey "permission byte != 1" "es[1]['bytes'][8] = 0"
broken uniq "instance step of 2" "[e.__setitem__('tau', e['tau'] + 2) for e in es[3:]]"
# control: one instance, keys 0 < 1 < … (honest); then the same with two keys swapped
U1="T = es[0]['tau']; [e.update(tau=T, bytes=[i] + [0]*31) for i, e in enumerate(es)]"
broken uniq "keys not sorted" "$U1; es[2]['bytes'], es[3]['bytes'] = es[3]['bytes'], es[2]['bytes']"
f="$rd/control-uniq"
"$npudr" v3sample uniq 7 5 | python3 -c "import json,sys; es=json.load(sys.stdin); $U1; print(json.dumps(es))" > "$f.json"
if "$npudr" v3check "$out/nearAirV3.json" uniq "$f.json" >"$f.check"; then pass "uniq control (sorted single instance) holds"
else bad "uniq control fails"; fi
broken walk "broken edge chain" "es[0]['steps'][1]['e'][0] += 1"
broken walk "first row not START" "es[1]['steps'][0]['sym'] = 3; es[1]['steps'][0]['e'][2] = 3"
# `acct` pre amount all-255 makes `dsum` zero so the inverse constraint fails
broken acct "pre amount is u128::MAX" "es[0]['pre'] = [255]*16 + es[0]['pre'][16:]"
broken size "x_0 + x_1 over 3,000,000" "es[0]['x0'] = 2000000; es[0]['x1'] = 2000000"
# `srcp`: a path item's carry length must be `32` on the first segment, else `64`
broken srcp "first path item pl != 32" "es[1]['path'][0]['pl'] = 64"
# `srcp`: a duplicate source key must have the empty-list length `L = 12`
broken srcp "dup with L != 12" "es[0]['dup'] = True"
# `qv`: the last main walk must end the table (`final`/`wend`), followed by a parser row
broken qv "last walk not final" "es['walks'][-1]['final'] = False"
# `qv`: main walks carry `tau = 0`; an implicit walk in the main segment is rejected
broken qv "main walk with tau != 0" "es['walks'][0]['tau'] = 1"

echo "== sizeV3 nonzero public overhead (PH_WOVH): Rust vs Lean, byte-identical"
# `npudr v3sample size` fixes `ovh = 0` so `v3check` (zero public inputs) passes.
# Here the public `u32` at `PH_WOVH = 198` is nonzero: the two renderers must
# still agree on the trace (this is the size differential's `ovh` field).
for ovh in 1 258 16909060; do
  for xs in "100 200 300" "1000000 1000000 500000" "2999999 1 0"; do
    set -- $xs; f="$rd/size-ovh-$ovh-$1-$2-$3"
    printf '[{"x0":%s,"x1":%s,"x2":%s,"ovh":%s}]\n' "$1" "$2" "$3" "$ovh" > "$f.json"
    if ! $HEAVY "$lr" size "$f.json" "$f.lean.bin" 2>"$f.err"; then bad "size ovh=$ovh x=$xs: np-lean-render-v3 failed"; cat "$f.err"; continue; fi
    "$npudr" v3render size "$f.json" "$f.rust.bin" || { bad "size ovh=$ovh x=$xs: npudr v3render failed"; continue; }
    if cmp -s "$f.lean.bin" "$f.rust.bin"; then pass "size ovh=$ovh x=($xs) trace identical ($(stat -c %s "$f.rust.bin") B)"
    else bad "size ovh=$ovh x=($xs) trace differs"; fi
  done
done

echo "== nearAirV3 honest entries from a real witness (part 2c): np-lean-entries-v3 vs Rust"
# `np-lean-entries-v3 <case>` runs the proved D0a extraction on a real fixture and
# dumps the per-table entry lists.  Node entries are the highest-value table: the
# Rust `v3render` must be byte-identical to `np-lean-render-v3` and `v3check` must
# accept every nearAirV3 constraint.  The Lean renderer recomputes the record lists
# per cell and is very slow for node (>2.5 min for 3 records, ~1 min/byte-ish), so
# by default `node` is only rendered by Lean for the smallest cases (≤
# `ENTRIES_NODE_MAX` records), while `v3check` always runs.  `val`/`head` render
# in seconds.
le3="$here/.lake/build/bin/np-lean-entries-v3"
fx="$here/../../../oracle/fixtures/v3/public-d0a/d0"
ed="$out/entries"; mkdir -p "$ed"
ncase=0; nrendered=0
for case in $(ls "$fx" | head -${ENTRIES_CASES:-5}); do
  d="$fx/$case"
  [ -f "$d/witness.bin" ] || continue
  for t in ${ENTRIES_TABLES:-node val head}; do
    j="$ed/$case.$t.json"
    if ! $HEAVY "$le3" "$d" $t > "$j" 2>"$j.err"; then bad "$case $t: np-lean-entries-v3 failed"; cat "$j.err"; continue; fi
    if ! "$npudr" v3check "$out/nearAirV3.json" $t "$j" >"$j.check" 2>&1; then
      bad "$case $t: v3check rejects honest entries"; head -3 "$j.check"; continue
    fi
    ncase=$((ncase + 1))
    ok="$(sed -n '1p' "$j.check" | cut -c5-)"
    # Lean render + byte compare: always for val/head; node only for the small cases
    do_render=1
    if [ "$t" = node ]; then
      nr=$(python3 -c "import json;print(len(json.load(open('$j'))))")
      if [ "$nr" -gt "${ENTRIES_NODE_MAX:-3}" ] && [ "${ENTRIES_NODE_ALL:-0}" != 1 ]; then
        do_render=0; pass "$case $t: $ok ($nr entries; Lean render skipped, over node-max)"
      fi
    fi
    [ "$do_render" = 1 ] || continue
    "$npudr" v3render $t "$j" "$j.rust.bin" || { bad "$case $t: npudr v3render failed"; continue; }
    $HEAVY "$lr" $t "$j" "$j.lean.bin" 2>"$j.lrerr" || { bad "$case $t: np-lean-render-v3 failed"; cat "$j.lrerr"; continue; }
    nrendered=$((nrendered + 1))
    if cmp -s "$j.lean.bin" "$j.rust.bin"; then
      pass "$case $t: $ok; Rust==Lean ($(stat -c %s "$j.rust.bin") B)"
    else bad "$case $t: Rust and Lean traces differ"; fi
  done
done
[ $ncase -gt 0 ] || bad "no fixture case produced honest entries"
echo "   ($ncase honest entry lists checked, $nrendered byte-compared against Lean)"

echo "== nearAirV3 SHA message collector (tables 0/1): npudr v3sha vs np-lean-entries-v3 sha"
# The SHA tables have no entries of their own: their input is the union of the
# BYTES/DIGEST messages of the other tables.  `np-lean-entries-v3 <case> sha`
# collects them in Lean; the Rust collector must produce byte-identical
# `{sha_t, sha_r}` message lists (deduplicated by id, split by the §12 kinds).
# The trace differential (`npudr v3render sha_t` vs `np-lean-render-v3 sha_t`) is
# O(rows²) in the Lean renderer, so it is opt-in via `SHA_RENDER=1`.
sd="$out/sha"; mkdir -p "$sd"
nsha=0
for case in $(ls "$fx" | head -${SHA_CASES:-5}); do
  d="$fx/$case"
  [ -f "$d/witness.bin" ] || continue
  # the collector wants plain `<table>.json` names
  cdir="$sd/$case.ent"; mkdir -p "$cdir"
  for t in node val head; do
    j="$ed/$case.$t.json"
    [ -f "$j" ] || $HEAVY "$le3" "$d" $t > "$j" 2>"$j.err"
    cp -f "$j" "$cdir/$t.json"
  done
  lj="$sd/$case.lean.json"
  if ! $HEAVY "$le3" "$d" sha > "$lj" 2>"$lj.err"; then bad "$case sha: np-lean-entries-v3 sha failed"; cat "$lj.err"; continue; fi
  if ! "$npudr" v3sha "$cdir" "$sd/$case.rust.t.json" "$sd/$case.rust.r.json" 2>"$sd/$case.err"; then
    bad "$case sha: npudr v3sha failed"; cat "$sd/$case.err"; continue
  fi
  python3 - "$lj" "$sd/$case.lean.t.json" "$sd/$case.lean.r.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
json.dump(d["sha_t"], open(sys.argv[2], "w"))
json.dump(d["sha_r"], open(sys.argv[3], "w"))
PY
  norm() { python3 -c "import json,sys;print(sorted((m['id'],bytes(m['bytes']),m['dmult']) for m in json.load(open(sys.argv[1]))))" "$1"; }
  if [ "$(norm "$sd/$case.lean.t.json")" = "$(norm "$sd/$case.rust.t.json")" ] && \
     [ "$(norm "$sd/$case.lean.r.json")" = "$(norm "$sd/$case.rust.r.json")" ]; then
    nt=$(python3 -c "import json;print(len(json.load(open('$sd/$case.lean.t.json'))))")
    nr=$(python3 -c "import json;print(len(json.load(open('$sd/$case.lean.r.json'))))")
    pass "$case sha: sha_t($nt) sha_r($nr) messages identical"
    nsha=$((nsha + 1))
    if [ "${SHA_RENDER:-0}" = 1 ] && [ "$nt" -gt 0 ]; then
      for t in sha_t sha_r; do
        "$npudr" v3render $t "$sd/$case.lean.$t.json" "$sd/$case.$t.rust.bin" || { bad "$case $t: v3render failed"; continue; }
        $HEAVY "$lr" $t "$sd/$case.lean.$t.json" "$sd/$case.$t.lean.bin" 2>"$sd/$case.$t.lrerr" || { bad "$case $t: np-lean-render-v3 failed"; continue; }
        cmp -s "$sd/$case.$t.lean.bin" "$sd/$case.$t.rust.bin" \
          && pass "$case $t: trace identical ($(stat -c %s "$sd/$case.$t.rust.bin") B)" \
          || bad "$case $t: trace differs"
      done
    fi
  else bad "$case sha: message lists differ"; fi
done
[ $nsha -gt 0 ] || bad "no fixture produced SHA messages"
echo "   ($nsha fixtures: SHA message lists byte-identical; trace render $([ "${SHA_RENDER:-0}" = 1 ] && echo on || echo off))"

echo "== prepD0 / Hint codec (part 3): Rust re-encode vs Lean np-lean-prep-v3"
# For each real D0a fixture: `np-lean-prep-v3` requires `checkD0a B0` and dumps
# `hint`, `prep`, `refunds_enc` and `prep_json`; the Rust `Prep.encode` of
# `prep_json` must reproduce `prep` byte for byte, the `Hint` codec must
# round-trip the Lean hint bytes, and `decodeBody(bodyOf refunds) = refunds`.
lp="$here/.lake/build/bin/np-lean-prep-v3"
pd="$out/prep"; mkdir -p "$pd"
nprep=0
for case in $(ls "$fx" | head -${PREP_CASES:-64}); do
  d="$fx/$case"
  [ -f "$d/claim.bin" ] && [ -f "$d/witness.bin" ] || continue
  j="$pd/$case.json"
  if ! $HEAVY "$lp" "$d" > "$j" 2>"$j.err"; then bad "$case prep: np-lean-prep-v3 failed"; cat "$j.err"; continue; fi
  nprep=$((nprep + 1))
  # extract the Lean `prep`, `hint` and `refunds_enc` hex fields once
  python3 - "$j" "$j.prep.bin" "$j.hint.bin" "$j.refunds.bin" <<'PY'
import json, sys
j = json.load(open(sys.argv[1]))
for key, path in (("prep", sys.argv[2]), ("hint", sys.argv[3]), ("refunds_enc", sys.argv[4])):
    open(path, "wb").write(bytes.fromhex(j[key]))
PY
  # Rust `Prep.encode` of the Lean `prep_json` vs the Lean `prep` bytes
  if ! "$npudr" prep-encode "$j" "$j.rust.bin" 2>"$j.rust.err"; then
    bad "$case prep: npudr prep-encode failed"; cat "$j.rust.err"; continue
  fi
  if cmp -s "$j.prep.bin" "$j.rust.bin"; then pass "$case prep: Prep.encode byte-identical ($(stat -c %s "$j.rust.bin") B)"
  else bad "$case prep: Prep.encode differs"; fi
  # Hint codec round-trips the Lean hint bytes
  if "$npudr" prep-hint "$j.hint.bin" "$j.hint.rt.bin" 2>"$j.hint.err" && \
     cmp -s "$j.hint.bin" "$j.hint.rt.bin"; then
    pass "$case prep: Hint codec round-trips ($(stat -c %s "$j.hint.bin") B)"
  else bad "$case prep: Hint codec round-trip failed"; cat "$j.hint.err"; fi
  # refund body codec: decodeBody(bodyOf refunds) = refunds
  if "$npudr" prep-body "$j.refunds.bin" "$j.refunds.rt.bin" 2>"$j.body.err" && \
     cmp -s "$j.refunds.bin" "$j.refunds.rt.bin"; then
    pass "$case prep: refund body codec round-trips"
  else bad "$case prep: refund body codec failed"; cat "$j.body.err"; fi
done
[ $nprep -gt 0 ] || bad "no fixture case produced a prepared statement"
echo "   ($nprep prepared statements re-encoded byte-for-byte)"

echo "== prepared public tape (Public.preparedBytes): Rust (npudr v3public) vs Lean"
ppd="$out/public"; mkdir -p "$ppd"
_pubcases=($(ls -d "$here/../../../oracle/fixtures/v3/public-d0a/d0"/* 2>/dev/null | head -${PUBLIC_MAX:-64}))
for d in "${_pubcases[@]}"; do
  [ -d "$d" ] || continue
  j="$ppd/$(basename "$d").json"
  if ! "$here/.lake/build/bin/np-lean-prep-v3" "$d" "$j" 2>"$ppd/$(basename "$d").err"; then continue; fi
  python3 - "$j" "$ppd/lean.hex" "$ppd/prep.json" <<'PY'
import json,sys
d=json.load(open(sys.argv[1]))
open(sys.argv[2],'w').write(d["public"])
open(sys.argv[3],'w').write(json.dumps(d["prep_json"]))
PY
  "$npudr" v3public "$ppd/prep.json" "$ppd/rust.bin" >/dev/null 2>&1 || { bad "public $(basename "$d"): npudr v3public failed"; continue; }
  if [ "$(python3 -c "print(open('$ppd/lean.hex').read().strip())")" = "$(python3 -c "print(open('$ppd/rust.bin','rb').read().hex())")" ]; then
    pass "public $(basename "$d") byte-identical"
  else bad "public $(basename "$d") differs"; fi
done

echo "== D0 native preprocessing (prepD0): Rust (npudr d0-prep) vs Lean np-lean-prep-v3"
# `np-lean-prep-v3` requires `checkD0a B0` and dumps `hint`/`prep`/`prep_json`;
# `npudr d0-prep` reads the real `claim.bin` + the Lean hint bytes and runs the
# ported `prepClaim`/`prepBody`.  The Rust `Prep.encode` (of the Rust prep_json)
# must equal the Lean `prep` byte for byte, so the two implementations agree on
# the whole prepared statement.  `PREP_D0_MAX` defaults to 64.
d0pd="$out/d0prep"; mkdir -p "$d0pd"
nd0=0
for case in $(ls "$fx" | head -${PREP_D0_MAX:-64}); do
  d="$fx/$case"
  [ -f "$d/claim.bin" ] && [ -f "$d/witness.bin" ] || continue
  j="$d0pd/$case.json"
  if ! $HEAVY "$lp" "$d" > "$j" 2>"$j.err"; then bad "$case d0-prep: np-lean-prep-v3 failed"; continue; fi
  python3 - "$j" "$d0pd/$case.hint" "$d0pd/$case.lean.prep" <<'PY'
import json,sys
d=json.load(open(sys.argv[1]))
open(sys.argv[2],'wb').write(bytes.fromhex(d['hint']))
open(sys.argv[3],'wb').write(bytes.fromhex(d['prep']))
PY
  nd0=$((nd0 + 1))
  if ! "$npudr" d0-prep "$d/claim.bin" "$d0pd/$case.hint" "$d0pd/$case.mine.json" >"$d0pd/$case.out" 2>"$d0pd/$case.mine.err"; then
    bad "$case d0-prep: npudr d0-prep failed"; cat "$d0pd/$case.mine.err"; continue
  fi
  if ! "$npudr" prep-encode "$d0pd/$case.mine.json" "$d0pd/$case.mine.prep" 2>"$d0pd/$case.enc.err"; then
    bad "$case d0-prep: npudr prep-encode failed"; cat "$d0pd/$case.enc.err"; continue
  fi
  if cmp -s "$d0pd/$case.lean.prep" "$d0pd/$case.mine.prep"; then
    pass "$case d0-prep: Prep.encode byte-identical ($(stat -c %s "$d0pd/$case.mine.prep") B)"
  else
    bad "$case d0-prep: Prep.encode differs"
  fi
done
[ $nd0 -gt 0 ] || bad "no fixture case produced a D0 prep"
echo "   ($nd0 native prepD0 statements byte-compared against Lean)"

echo "== prover preprocessing (hintOf + prepD0): Rust (npudr v3prepare) vs Lean (np-lean-prep-v3 --any)"
# The total differential: `npudr v3prepare` computes the hint itself (`v3::hint` =
# `NearSpecV3.hintOf`) and runs `v3::d0::prep` (= `prepD0`); `np-lean-prep-v3 --any`
# reports `checkD0a B0`, `Hint.encode (hintOf cb wb)` and `prepD0 cb h` without
# requiring acceptance.  On every fixture the hint bytes, the accept/reject verdict of
# `prepD0` and the `Prep.encode` bytes must agree.  Then mutated cases
# (`MUTATE_CASES` fixtures, default 4):
# * claim mutations (pv, A12 extra boundary, tx flags, genesis extra, epoch start,
#   chunk-inner gas_used / receipts root, RS params, truncation): Lean `checkD0a B0`
#   must reject and Rust `v3prepare` must reject too (and agree with Lean `prepD0`);
# * hint mutations (`--hint`: n+1, trailing body byte, empty hint): Rust and Lean
#   `prepD0` must both reject;
# * witness mutations (byte flips, truncation): the Rust hint must equal Lean's
#   `hintOf` and the `prepD0` verdicts must agree.
vd="$out/v3prepare"; mkdir -p "$vd"
cat > "$vd/mutate.py" <<'PYEOF'
import struct, sys
def u32(b, p): return struct.unpack_from('<I', b, p)[0]
def parse(b):
    """Offsets of the `claim.bin` fields (`decodeClaimE` order)."""
    o = {}; p = 0
    def by():
        nonlocal p
        n = u32(b, p); s = p; p += 4 + n
        return s, n
    by(); by()                                   # format tag, statement id
    o['pv'] = p; p += 4
    by(); p += 32                                # chain_id, epoch_id
    o['inner'] = by()[0] + 4                     # chunk_inner data
    nb = u32(b, p); p += 4
    for _ in range(nb):
        p += 1 + 32; by(); by()
        ns = u32(b, p); p += 4
        for _ in range(ns):
            by(); p += 8
    o['rs'] = p; p += 4
    ne = u32(b, p); p += 4
    for i in range(ne):
        p += 32 + 4 + 8
        s, n = by()
        if i == 0: o['layout'] = (s, n)
        nv = u32(b, p); p += 4
        for _ in range(nv):
            by(); p += 16
    o['esa'] = by()
    nf = u32(b, p); p += 4
    for _ in range(nf):
        t = b[p]; p += 1
        if t == 1:
            for _ in range(2):
                k = u32(b, p); p += 4
                for _ in range(k):
                    by(); p += 16
            t2 = b[p]; p += 1
            if t2 == 1: by()
        p += 16
        t = b[p]; p += 1
        if t == 1:
            p += 24
            for _ in range(2):
                k = u32(b, p); p += 4 + 8 * k
    o['txv'] = by()
    o['gce'] = p
    assert b[p] == 0 and p + 1 == len(b), 'unexpected claim tail'
    return o
def mutate(b, kind):
    o = parse(b); b = bytearray(b)
    if kind == 'pv': struct.pack_into('<I', b, o['pv'], 87)
    elif kind == 'a12':                          # one surplus boundary account
        s, n = o['layout']; lay = bytes(b[s + 4:s + 4 + n])
        nbd = u32(lay, 1); q = 5
        for _ in range(nbd): q += 4 + u32(lay, q)
        extra = b'zzzzzzzzzz'
        lay2 = lay[:1] + struct.pack('<I', nbd + 1) + lay[5:q] + struct.pack('<I', len(extra)) + extra + lay[q:]
        b = b[:s] + struct.pack('<I', len(lay2)) + lay2 + b[s + 4 + n:]
    elif kind == 'txv':
        s, n = o['txv']
        b = b[:s] + struct.pack('<I', n + 1) + b[s + 4:s + 4 + n] + b'\x01' + b[s + 4 + n:]
    elif kind == 'gce': b = b[:o['gce']] + b'\x01' + struct.pack('<I', 1) + b'\x00'
    elif kind == 'esa':
        s, n = o['esa']
        if n == 0: raise SystemExit(3)
        b[s + 4] = 1
    elif kind == 'gasused': b[o['inner'] + 153] ^= 1     # ChunkInner.prev_gas_used
    elif kind == 'rcptroot': b[o['inner'] + 185] ^= 1    # prev_outgoing_receipts_root
    elif kind == 'rs': b[o['rs']] ^= 1                   # rs_data_parts
    elif kind == 'trunc': b = b[:-1]
    else: raise SystemExit('unknown mutation ' + kind)
    return bytes(b)
def wmutate(w, kind):
    w = bytearray(w)
    if kind == 'wtrunc': return bytes(w[:-1])
    if kind == 'wmid': w[len(w) // 2] ^= 0x40
    elif kind == 'wthird': w[len(w) // 3] ^= 0x01
    else: raise SystemExit('unknown mutation ' + kind)
    return bytes(w)
src, dst, kind = sys.argv[1:4]
d = open(src, 'rb').read()
open(dst, 'wb').write(wmutate(d, kind) if kind.startswith('w') else mutate(d, kind))
PYEOF
cat > "$vd/cmp.py" <<'PYEOF'
import json, os, sys
lj, rd, rc = sys.argv[1], sys.argv[2], int(sys.argv[3])
d = json.load(open(lj))
# with `--hint`, Rust's `hint.bin` is the given hint; Lean's `hint` is always `hintOf`,
# compared against the honest Rust hint (4th argument)
h = open(sys.argv[4] if len(sys.argv) > 4 else os.path.join(rd, 'hint.bin'), 'rb').read()
pp = os.path.join(rd, 'prep.bin')
hint_ok = bytes.fromhex(d['hint']) == h
if d['prep'] is None: prep_ok = rc == 1
else: prep_ok = rc == 0 and os.path.exists(pp) and open(pp, 'rb').read() == bytes.fromhex(d['prep'])
print('%s %s %s' % ('hint_eq' if hint_ok else 'hint_DIFF', 'prep_eq' if prep_ok else 'prep_DIFF',
                    'check_ok' if d['check'] == 'ok' else 'check_rej'))
PYEOF
lp="$here/.lake/build/bin/np-lean-prep-v3"
# vcase <label> <claim> <witness> [<hint.bin> <honest hint.bin>] -> prints the cmp.py verdict line
vcase() {
  local lbl="$1" cb="$2" wb="$3" hb="${4:-}" hh="${5:-}" rc
  rm -rf "$vd/$lbl.rust"
  if [ -n "$hb" ]; then
    "$npudr" v3prepare "$cb" "$wb" "$vd/$lbl.rust" --hint "$hb" > "$vd/$lbl.out" 2>&1; rc=$?
    $HEAVY "$lp" --any "$cb" "$wb" "$hb" > "$vd/$lbl.lean.json" 2>"$vd/$lbl.lean.err" || { echo "lean_failed"; return; }
  else
    "$npudr" v3prepare "$cb" "$wb" "$vd/$lbl.rust" > "$vd/$lbl.out" 2>&1; rc=$?
    $HEAVY "$lp" --any "$cb" "$wb" > "$vd/$lbl.lean.json" 2>"$vd/$lbl.lean.err" || { echo "lean_failed"; return; }
  fi
  [ $rc -le 1 ] || { echo "rust_failed"; return; }
  python3 "$vd/cmp.py" "$vd/$lbl.lean.json" "$vd/$lbl.rust" $rc $hh
}
nv=0
for case in $(ls "$fx" | head -${PREPARE_MAX:-64}); do
  d="$fx/$case"
  [ -f "$d/claim.bin" ] && [ -f "$d/witness.bin" ] || continue
  r=$(vcase "$case" "$d/claim.bin" "$d/witness.bin")
  if [ "$r" = "hint_eq prep_eq check_ok" ]; then
    pass "$case v3prepare: hintOf + prepD0 byte-identical ($(cat "$vd/$case.out"))"; nv=$((nv + 1))
  else bad "$case v3prepare: $r"; fi
done
[ $nv -gt 0 ] || bad "no fixture case accepted by v3prepare"
echo "   ($nv fixtures: Rust hintOf + prepD0 byte-identical to Lean)"
nm=0
for case in $(ls "$fx" | head -${MUTATE_CASES:-4}); do
  d="$fx/$case"
  [ -f "$d/claim.bin" ] && [ -f "$d/witness.bin" ] || continue
  for kind in pv a12 txv gce esa gasused rcptroot rs trunc; do
    lbl="$case.$kind"
    python3 "$vd/mutate.py" "$d/claim.bin" "$vd/$lbl.claim" $kind 2>"$vd/$lbl.merr" || continue
    r=$(vcase "$lbl" "$vd/$lbl.claim" "$d/witness.bin")
    case "$r" in
      "hint_eq prep_eq check_rej")
        if grep -q '^reject:' "$vd/$lbl.out"; then
          pass "$lbl: checkD0a rejects, v3prepare rejects ($(sed 's/^reject: //' "$vd/$lbl.out" | cut -c1-90))"; nm=$((nm + 1))
        else bad "$lbl: checkD0a rejects but v3prepare accepts"; fi ;;
      *) bad "$lbl: $r" ;;
    esac
  done
  # hint mutations on the honest claim: `prepD0` must reject in both
  hb="$vd/$case.rust/hint.bin"
  [ -f "$hb" ] || "$npudr" v3prepare "$d/claim.bin" "$d/witness.bin" "$vd/$case.rust" > /dev/null
  python3 - "$hb" "$vd/$case" <<'PYEOF'
import struct, sys
h = open(sys.argv[1], 'rb').read(); n = struct.unpack_from('<I', h)[0]
body = h[8:]
open(sys.argv[2] + '.hn.bin', 'wb').write(struct.pack('<I', n + 1) + h[4:])
b2 = body + b'\x00'
open(sys.argv[2] + '.hb.bin', 'wb').write(h[:4] + struct.pack('<I', len(b2)) + b2)
open(sys.argv[2] + '.he.bin', 'wb').write(struct.pack('<I', 0) + struct.pack('<I', 8) + bytes(8))  # Hint.empty
PYEOF
  for hk in hn hb he; do
    lbl="$case.$hk"
    r=$(vcase "$lbl" "$d/claim.bin" "$d/witness.bin" "$vd/$case.$hk.bin" "$hb")
    if [ "$r" = "hint_eq prep_eq check_ok" ] && grep -q '^reject:' "$vd/$lbl.out"; then
      pass "$lbl: mutated hint rejected by Rust and Lean prepD0 ($(sed 's/^reject: //' "$vd/$lbl.out" | cut -c1-70))"; nm=$((nm + 1))
    elif [ "$hk" = he ] && [ "$r" = "hint_eq prep_eq check_ok" ]; then
      # the empty hint is the honest hint when there are no receipts and no refunds
      pass "$lbl: empty hint, Rust and Lean prepD0 agree ($(head -c 60 "$vd/$lbl.out"))"; nm=$((nm + 1))
    else bad "$lbl: $r ($(cat "$vd/$lbl.out"))"; fi
  done
  # witness mutations: hint bytes and prepD0 verdicts must agree
  for kind in wthird wtrunc wmid; do
    lbl="$case.$kind"
    python3 "$vd/mutate.py" "$d/witness.bin" "$vd/$lbl.witness" $kind || continue
    r=$(vcase "$lbl" "$d/claim.bin" "$vd/$lbl.witness")
    case "$r" in
      "hint_eq prep_eq "*) pass "$lbl: hintOf + prepD0 agree on the mutated witness (${r##* }; $(head -c 60 "$vd/$lbl.out"))"; nm=$((nm + 1)) ;;
      *) bad "$lbl: $r" ;;
    esac
  done
done
echo "   ($nm mutated claim/hint/witness cases agree; every checkD0a-rejected claim is rejected)"

echo
if [ $fail -eq 0 ]; then echo "ALL PASS"; else echo "SOME FAILED"; fi
exit $fail
