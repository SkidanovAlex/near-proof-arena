# run-v2.d/a7.sh — the A7 tables of nearAirV3 (sourced by run-v2.sh / run-v2-section.sh a7;
# in scope: here src out npudr lr le le3 lp fx HEAVY pass bad).
#
# `nodeA7` (2), `valA7` (4), `upsA7` (7), `sizeA7` (21) (`Tables/UnfoldA7.lean`) are the base
# tables with the A7 accounting columns appended; the honest renders are `nodeA7Trace`,
# `valA7Trace`, `upsA7Trace`, `sizeA7Trace` (`Render/UnfoldA7Aligned.lean`), run by
# `np-lean-render-v3-a7` (RenderV3A7.lean) and compared byte for byte with `npudr v3render`.
# Entry inputs: node/val entries carry an optional `"rpl": bool` (replaced record), the size
# entry an optional `"yN": [y0, y1, y2]` (received A7 totals); absent → false / zeros.
#
# Knobs: A7_SEEDS (1 2 3), A7_NODE_SIZES (1 2; Lean node render is slow), A7_VAL_SIZES
# (0 1 5 37), A7_UPS_SIZES (0 1 3), A7_CASES (3 real fixture cases), A7_NODE_MAX (3: Lean
# render of fixture node entries only up to this many records).
a7="$out/a7"; mkdir -p "$a7"
la7="$here/.lake/build/bin/np-lean-render-v3-a7"
air="$out/nearAirV3.json"

echo "== A7 tables: widths / maxLog in the nearAirV3 export"
if python3 - "$air" <<'PY'
import json, sys
ts = json.load(open(sys.argv[1]))["tables"]
want = {2: (188, 22), 4: (17, 22), 7: (202, 22), 21: (57, 4)}
ok = True
for i, (w, m) in want.items():
    t = ts[i]
    got = (t["width"], t.get("maxLog", t.get("max_log")))
    print(f"   table {i}: width {got[0]} maxLog {got[1]} (want {w} {m})")
    ok &= got == (w, m)
sys.exit(0 if ok else 1)
PY
then pass "A7 table widths/maxLog match (188/22, 17/22, 202/22, 57/4)"
else bad "A7 table widths/maxLog differ from the expected nodeA7/valA7/upsA7/sizeA7"; fi
if "$npudr" layout "$air" 2 > "$a7/layout.txt" 2>&1; then
  pass "npudr layout (aux group 2): $(awk '$1==2||$1==4||$1==7||$1==21{printf "t%s w%s aux%s; ", $1, $2, $3}' "$a7/layout.txt")"
else bad "npudr layout failed"; cat "$a7/layout.txt"; fi

# a7cmp <table> <json> <label>: Rust vs Lean, byte-identical
a7cmp() {
  local t=$1 f=$2 x=$3
  if ! $HEAVY "$la7" $t "$f" "$f.lean.bin" 2>"$f.err"; then bad "$t $x: np-lean-render-v3-a7 failed"; cat "$f.err"; return 1; fi
  if ! "$npudr" v3render $t "$f" "$f.rust.bin" 2>"$f.rerr"; then bad "$t $x: npudr v3render failed"; cat "$f.rerr"; return 1; fi
  if cmp -s "$f.lean.bin" "$f.rust.bin"; then pass "$t $x: Rust==Lean ($(stat -c %s "$f.rust.bin") B)"
  else bad "$t $x: Rust and Lean traces differ"; return 1; fi
}
# a7check <table> <json> <label>: every nearAirV3 constraint of the table holds
a7check() {
  local t=$1 f=$2 x=$3
  if "$npudr" v3check "$air" $t "$f" >"$f.check" 2>&1; then pass "$t $x: $(cut -c5- "$f.check")"
  else bad "$t $x: constraints fail"; head -3 "$f.check"; fi
}
# a7reject <table> <json> <label>: the rendered trace must violate a constraint
a7reject() {
  local t=$1 f=$2 x=$3
  if "$npudr" v3check "$air" $t "$f" >"$f.check" 2>&1; then bad "$t $x: constraints still hold"
  else pass "$t $x: constraint violated ($(head -1 "$f.check"))"; fi
}

echo "== A7 renders: Rust (npudr v3render) vs Lean (np-lean-render-v3-a7), sampled entries"
# node/ups samples are shape-valid, not honest (node entries come from the witness; no
# UpsRenderOk sampler exists), so only val/size samples are also run through v3check.
for t in node val ups size; do
  case $t in
    node) ns="${A7_NODE_SIZES:-1 2}";; val) ns="${A7_VAL_SIZES:-0 1 5 37}";;
    ups) ns="${A7_UPS_SIZES:-0 1 3}";; size) ns=1;;
  esac
  for seed in ${A7_SEEDS:-1 2 3}; do
    for n in $ns; do
      f="$a7/$t-$seed-$n.json"
      "$npudr" v3sample $t $seed $n > "$f" || { bad "$t seed=$seed n=$n: v3sample failed"; continue; }
      a7cmp $t "$f" "seed=$seed n=$n"
      case $t in val|size) a7check $t "$f" "seed=$seed n=$n";; esac
    done
  done
done

echo "== A7 renders: edge inputs (empty lists, absent rpl/yN, the B0 bound)"
for t in node val ups; do
  f="$a7/$t-empty.json"; echo '[]' > "$f"; a7cmp $t "$f" "empty list"
done
a7check val "$a7/val-empty.json" "empty list"
# `upsV3` is not admitted empty (`UpsNativeOk`: at least one instance; a base constraint fails)
a7reject ups "$a7/ups-empty.json" "empty list (no instance)"
# the pre-A7 entry format (no `rpl`, no `yN`): read as all-false / zeros
f="$a7/val-norpl.json"
"$npudr" v3sample val 5 9 | python3 -c "import json,sys; es=json.load(sys.stdin); [e.pop('rpl') for e in es]; print(json.dumps(es))" > "$f"
a7cmp val "$f" "no rpl fields"; a7check val "$f" "no rpl fields"
f="$a7/val-allrpl.json"
"$npudr" v3sample val 5 9 | python3 -c "import json,sys; es=json.load(sys.stdin); [e.update(rpl=True) for e in es]; print(json.dumps(es))" > "$f"
a7cmp val "$f" "every record replaced"; a7check val "$f" "every record replaced"
f="$a7/node-allrpl.json"
"$npudr" v3sample node 5 2 | python3 -c "import json,sys; es=json.load(sys.stdin); [e.update(rpl=True) for e in es]; print(json.dumps(es))" > "$f"
a7cmp node "$f" "every record replaced"
for ys in "none" "0 0 0" "2000000 0 0" "1 1999998 1" "700000 600000 700001" "2000000 1 0"; do
  f="$a7/size-y-${ys// /-}.json"
  if [ "$ys" = none ]; then echo '[{"x0":5,"x1":6,"x2":7,"ovh":0}]' > "$f"
  else set -- $ys; printf '[{"x0":5,"x1":6,"x2":7,"ovh":0,"yN":[%s,%s,%s]}]\n' $1 $2 $3 > "$f"; fi
  a7cmp size "$f" "yN=($ys)"
  case "$ys" in
    "700000 600000 700001"|"2000000 1 0") a7reject size "$f" "yN=($ys): Σ y over B0 = 2,000,000";;
    *) a7check size "$f" "yN=($ys)";;
  esac
done
# a nonzero public overhead: the renderers agree (v3check supplies zero publics)
f="$a7/size-ovh.json"; echo '[{"x0":100,"x1":200,"x2":300,"ovh":16909060,"yN":[3,4,5]}]' > "$f"
a7cmp size "$f" "ovh=16909060"

echo "== A7 on real witness entries (np-lean-entries-v3 node/val), rpl absent and random"
# `np-lean-entries-v3` dumps the pre-A7 entry objects (no `rpl`): Rust reads them as all-false
# (`v3check` is local).  Then a seeded random `rpl` choice (any choice is locally legal).
na7=0
for case in $(ls "$fx" | head -${A7_CASES:-3}); do
  d="$fx/$case"
  [ -f "$d/witness.bin" ] || continue
  for t in node val; do
    j="$a7/$case.$t.json"
    if ! $HEAVY "$le3" "$d" $t > "$j" 2>"$j.err"; then bad "$case $t: np-lean-entries-v3 failed"; cat "$j.err"; continue; fi
    nr=$(python3 -c "import json;print(len(json.load(open('$j'))))")
    a7check $t "$j" "$case ($nr entries, no rpl)"
    jr="$a7/$case.$t.rpl.json"
    python3 -c "import json,random; random.seed('$case$t'); es=json.load(open('$j')); [e.update(rpl=random.random()<0.5) for e in es]; json.dump(es, open('$jr','w'))"
    a7check $t "$jr" "$case ($nr entries, random rpl)"
    na7=$((na7 + 1))
    if [ "$t" = node ] && [ "$nr" -gt "${A7_NODE_MAX:-3}" ]; then
      pass "$case $t: Lean render skipped ($nr records > A7_NODE_MAX)"; continue
    fi
    a7cmp $t "$jr" "$case ($nr entries, random rpl)"
  done
done
[ $na7 -gt 0 ] || bad "A7: no fixture case produced entries"
