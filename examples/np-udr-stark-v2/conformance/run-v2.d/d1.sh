# shellcheck shell=bash
# run-v2.d/d1.sh — D1 (nearAirV3D1, lane v3-d1-tables): the 30-table D1 pipeline on real D1a
# fixtures (sourced by run-v2.sh / run-v2-section.sh d1; in scope: here src out npudr HEAVY pass bad).
#
# Per fixture (public-d1/d1, the accepted public-d1a mutants `*at_bound`, and public-d0a/d0 run
# through the D1 path: D0a ⊂ D1a; D1_FX / D1_MAX restrict):
#   1. `npudr v3d1prove --check-only --dump`: every constraint of the 30 tables and the exact
#      balance of every bus (tables + the D1 public tape);
#   2. Lean `np-lean-d1-v3 entries` (instrumented replay of `processTxs` with the spec's own
#      functions) == the Rust `txV3` / `akmV3` entries (`tx.json`, `akm.json`);
#   3. Lean `np-lean-d1-v3 prep` (the verifier's native `prepD1` on the Rust hint) == the Rust
#      prepared tape, byte for byte;
#   4. negatives (fixtures with ops, first D1_NEG = 6): the hint's verdict bits of op 0 claimed
#      dishonestly (a flipped `ok`, a shifted `stage`) in the public op and the `txV3` trace
#      alike must fail the check.
d1o="$out/d1"; mkdir -p "$d1o"
ld1="$here/.lake/build/bin/np-lean-d1-v3"
air1="$out/nearAirV3D1.json"
[ -s "$air1" ] || "$here/.lake/build/bin/np-lean-export-v3d1" > "$air1"
F3="$here/../../../oracle/fixtures/v3"
echo "== d1: nearAirV3D1 check, Lean entries / prepD1 differential, negatives"
nneg=0
for d in ${D1_FX:-$F3/public-d1/d1/* $F3/public-d1a/mutants/*at_bound $F3/public-d0a/d0/*}; do
  [ -f "$d/witness.bin" ] || continue
  case=$(basename "$d"); p="$d1o/$case"; rm -rf "$p"
  if $HEAVY "$npudr" v3d1prove "$d" "$p" --air "$air1" --check-only --dump > "$p.log" 2>&1; then
    pass "$case: v3d1prove --check-only (30 tables, all buses)"
  else bad "$case: v3d1prove: $(grep -m2 'FAIL\|IMBAL\|npudr:' "$p.log" | tr '\n' ' ')"; continue; fi
  if "$ld1" entries "$d" > "$p/lean.json" 2> "$p/lean.err" && python3 - "$p" <<'PY'
import json, sys
p = sys.argv[1]; l = json.load(open(p + "/lean.json"))
sys.exit(0 if l["tx"] == json.load(open(p + "/tx.json")) and l["akm"] == json.load(open(p + "/akm.json")) else 1)
PY
  then pass "$case: Lean entries == Rust (txV3 / akmV3)"; else bad "$case: Lean entries differ"; fi
  if "$ld1" prep "$d" "$p/hint.bin" "$p/lean_prep.bin" 2> "$p/lprep.err" && cmp -s "$p/lean_prep.bin" "$p/prepared.bin"; then
    pass "$case: Lean prepD1 tape == Rust tape"; else bad "$case: prepD1 tape differs ($(cat "$p/lprep.err"))"; fi
  ops=$(python3 -c "import json;print(json.load(open('$p/report.json'))['ops'])")
  if [ "$ops" -gt 0 ] && [ "$nneg" -lt "${D1_NEG:-6}" ]; then
    nneg=$((nneg + 1))
    for m in 0:ok 0:stage; do
      if $HEAVY "$npudr" v3d1prove "$d" "$p.neg" --air "$air1" --check-only --mutate-op "$m" > "$p.neg.log" 2>&1; then
        bad "$case: mutated op $m accepted"; else pass "$case: mutated op $m rejected"; fi
    done
    rm -rf "$p.neg"
  fi
  rm -f "$p/prepared.bin" "$p/lean_prep.bin"
done
