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
#    aligned generator (Render/Padded.lean, Render/PaddedTrie.lean), seeded
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
(cd "$here" && $HEAVY lake build -q np-lean-verify-v2 np-lean-export-v3 np-lean-render-v3) || { echo "lake build failed"; exit 2; }
npudr="$src/target/release/npudr"
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
for t in ${RENDER_TABLES:-bnd akey head val uniq walk}; do
  for seed in 1 2 3; do
    for n in ${RENDER_SIZES:-0 1 5 37}; do
      f="$rd/$t-$seed-$n"
      "$npudr" v3sample $t $seed $n > "$f.json"
      $HEAVY "$lr" $t "$f.json" "$f.lean.bin" 2>"$f.err" || { bad "$t seed=$seed n=$n: np-lean-render-v3 failed"; continue; }
      "$npudr" v3render $t "$f.json" "$f.rust.bin" || { bad "$t seed=$seed n=$n: npudr v3render failed"; continue; }
      if cmp -s "$f.lean.bin" "$f.rust.bin"; then pass "$t seed=$seed n=$n trace identical ($(stat -c %s "$f.rust.bin") B)"
      else bad "$t seed=$seed n=$n trace differs"; fi
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

echo
if [ $fail -eq 0 ]; then echo "ALL PASS"; else echo "SOME FAILED"; fi
exit $fail
