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
#      alike must fail the check;
#   5. (lane v3-d1-a7b, plan §5 R-5 → (B)) Lean `entries`'s `unread` (the walk terminal of every
#      `txKeys` entry, the stub windows, the `nmemV3` modes, the `uvalV3` values) == Rust's
#      `unread.json`; the AIR's A7 count (`a7_air` = Σ yN) == the Python D1a checker's
#      `unfold` (`checkD1`'s `unfoldBytesD1`, main pre trie over every `txKeys` entry);
#   6. negatives (first D1_NEG fixtures with local receipts): `--mutate-rid` (a `ridV3` row with
#      `i ≢ j (mod 32)` and the field slot `l = (j − i)/32`) must fail.
# Then the extra D1 fixtures (fixtures-extra/d1: the R-5 counterexample): steps 1, 2, 5, and the
# A7 bound mutants (the AIR's `B0` constant replaced by `unfold` / `unfold − 1`, `--a7-bound`):
# accept at `unfold`, reject at `unfold − 1`; and the D1a `*_over` mutants must be rejected.
d1o="$out/d1"; mkdir -p "$d1o"
ld1="$here/.lake/build/bin/np-lean-d1-v3"
air1="$out/nearAirV3D1.json"
[ -s "$air1" ] || "$here/.lake/build/bin/np-lean-export-v3d1" > "$air1"
F3="$here/../../../oracle/fixtures/v3"
echo "== d1: nearAirV3D1 check, Lean entries / prepD1 differential, negatives"
nneg=0
PYD1A="$here/../../../oracle/tools/spec_check_v3_d1a.py"
nrid=0
for d in ${D1_FX:-$F3/public-d1/d1/* $F3/public-d1a/mutants/*at_bound $F3/public-d0a/d0/* $here/fixtures-extra/d1/*}; do
  [ -f "$d/witness.bin" ] || continue
  case=$(basename "$d"); p="$d1o/$case"; rm -rf "$p"
  if $HEAVY "$npudr" v3d1prove "$d" "$p" --air "$air1" --check-only --dump > "$p.log" 2>&1; then
    pass "$case: v3d1prove --check-only (33 tables, all buses)"
  else bad "$case: v3d1prove: $(grep -m2 'FAIL\|IMBAL\|npudr:' "$p.log" | tr '\n' ' ')"; continue; fi
  if "$ld1" entries "$d" > "$p/lean.json" 2> "$p/lean.err" && python3 - "$p" <<'PY'
import json, sys
p = sys.argv[1]; l = json.load(open(p + "/lean.json"))
srt = lambda x: sorted(json.dumps(y) for y in x)
u, r = l["unread"], json.load(open(p + "/unread.json"))
ok = l["tx"] == json.load(open(p + "/tx.json")) and l["akm"] == json.load(open(p + "/akm.json")) and \
  u["terms"] == r["terms"] and all(srt(u[k]) == srt(r[k]) for k in ("stubs", "nmem", "uval"))
sys.exit(0 if ok else 1)
PY
  then pass "$case: Lean entries == Rust (txV3 / akmV3 / unread walks, stubs, nmemV3, uvalV3)"; else bad "$case: Lean entries differ"; fi
  unf=$(python3 "$PYD1A" "$d" 2>/dev/null | python3 -c "import json,sys;print(json.loads(sys.stdin.readline())['unfold'])")
  air=$(python3 -c "import json;print(json.load(open('$p/report.json'))['a7_air'])")
  if [ -n "$unf" ] && [ "$unf" = "$air" ]; then pass "$case: AIR A7 count $air == unfoldBytesD1"
  else bad "$case: AIR A7 count $air != unfoldBytesD1 $unf"; fi
  case "$d" in */fixtures-extra/d1/*)
    for B in "$unf" "$((unf - 1))"; do
      python3 - "$air1" "$p.air$B.json" "$B" <<'PY'
import json, sys
a = json.load(open(sys.argv[1])); n = 0
def walk(e):
    global n
    if isinstance(e, list):
        if len(e) == 2 and e[0] == 'c' and e[1] == 2000000:
            n += 1; return ['c', int(sys.argv[3])]
        return [walk(x) for x in e]
    return e
a['tables'][21]['constraints'] = [walk(c) for c in a['tables'][21]['constraints']]
assert n == 1
json.dump(a, open(sys.argv[2], 'w'))
PY
      if $HEAVY "$npudr" v3d1prove "$d" "$p.b$B" --air "$p.air$B.json" --check-only --a7-bound "$B" > "$p.b$B.log" 2>&1; then r=accept; else r=reject; fi
      if [ "$B" = "$unf" ]; then w=accept; else w=reject; fi
      if [ "$r" = "$w" ]; then pass "$case: A7 bound $B: $r"; else bad "$case: A7 bound $B: $r (want $w)"; fi
      rm -rf "$p.b$B" "$p.air$B.json"
    done ;;
  esac
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
  locs=$(python3 -c "import json;print(json.load(open('$p/report.json'))['locals'])")
  if [ "$locs" -gt 0 ] && [ "$nrid" -lt "${D1_NEG:-6}" ]; then
    nrid=$((nrid + 1))
    if $HEAVY "$npudr" v3d1prove "$d" "$p.rid" --air "$air1" --check-only --mutate-rid > "$p.rid.log" 2>&1; then
      bad "$case: ridV3 slot out of range accepted"; else pass "$case: ridV3 slot out of range rejected"; fi
    rm -rf "$p.rid"
  fi
  rm -f "$p/prepared.bin" "$p/lean_prep.bin"
done
for d in ${D1_OVER:-$F3/public-d1a/mutants/*_over}; do
  [ -f "$d/witness.bin" ] || continue
  case=$(basename "$d"); p="$d1o/$case"; rm -rf "$p"
  # accepted iff the AIR check passes and the verifier's native `prepD1` accepts the hint
  if $HEAVY "$npudr" v3d1prove "$d" "$p" --air "$air1" --check-only > "$p.log" 2>&1 &&
     "$ld1" prep "$d" "$p/hint.bin" "$p/lean_prep.bin" 2> "$p.lprep.err"; then
    bad "$case: over-bound D1a mutant accepted"
  else pass "$case: over-bound D1a mutant rejected ($(cat "$p.lprep.err" 2>/dev/null | head -c 120)$(grep -m1 'FAIL\|npudr:' "$p.log" | head -c 120))"; fi
  rm -rf "$p"
done
