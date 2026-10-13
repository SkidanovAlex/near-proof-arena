# shellcheck shell=bash
# run-v2.d/extra.sh — the prover differentials on the EXTRA D0a fixtures
# (`fixtures-extra/`, README there): repeated source keys (public dup byte 1, SrcpDD dup/rep
# rows, gated RC digests) and present-but-empty values (val `vz` rows, zero-length VPRE jobs),
# which the 64 public D0a fixtures never contain.  Sourced by run-v2.sh / run-v2-section.sh
# (in scope: here src out npudr lr le le3 lp fx HEAVY pass bad).
#
# 1. acceptance: Lean `checkD0a B0` (zk-formal `nearspec-v3-check-d0a`) and the Python
#    reference accept every `d0/` case and reject every `mutants/` case; D0a difftest 0
#    disagreements (`oracle/tools/difftest_v3_d0a.py`);
# 2. prepared statement: `np-lean-prep-v3` vs Rust — public tape (`v3public`) byte-identical,
#    `Prep.encode`, Hint codec, `d0-prep` (Lean hint), `v3prepare` (Rust hint + prep);
#    the tape's source rows `[dup, rep] ++ root` equal an independent recomputation of
#    `sourceDupByte` / `sourceRep` from the prep lists;
# 3. real-witness tables: `np-lean-entries-v3` node/val/head -> `v3check` (+ Lean render of
#    val (A7) / head); `np-lean-shabins-v3` -> `npudr v3sha` families + bins identical,
#    `v3check` of sha_t / sha_r; srcp (SrcpDD, `rep` = `sourceRep` of the prep lists) Rust ==
#    Lean render, `v3check`, and bus 14 (B_SRC) balanced against the public tape
#    (`npudr v3bus`); acct `v3check` + Rust == Lean render;
# 4. negatives: an inconsistent repeat (public dup byte 2: from-shard or root of a repeated
#    occurrence changed in the prepared lists) -> the tape row carries byte 2 and bus 14
#    cannot balance with the honest srcp table; a flipped `rep` bit also unbalances bus 14.
#
# Knobs: EXTRA_FX (default fixtures-extra), EXTRA_NODE_MAX (0: Lean node render skipped above
# this many records; the node table is v3check'ed always).
xf="${EXTRA_FX:-$here/fixtures-extra}"
xo="$out/extra"; rm -rf "$xo"; mkdir -p "$xo"
air="$out/nearAirV3.json"
lsb="$here/.lake/build/bin/np-lean-shabins-v3"
lrr="$here/.lake/build/bin/np-lean-render-v3-rcs"
la7="$here/.lake/build/bin/np-lean-render-v3-a7"
repo="$here/../../.."
chk="${CHECK_D0A:-$repo/zk-formal/.lake/build/bin/nearspec-v3-check-d0a}"

echo "== extra D0a fixtures: acceptance (Lean checkD0a B0, Python reference, difftest)"
if [ -x "$chk" ]; then
  if python3 "$repo/oracle/tools/difftest_v3_d0a.py" --cases "$xf" --lean "$chk" \
      --python "$repo/oracle/tools/spec_check_v3_d0a.py" --report "$xo/difftest.json" >/dev/null 2>"$xo/difftest.err" && \
     r=$(python3 - "$xo/difftest.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1])); c = r["counts"]
ok = (r["disagreements"] == 0 and c.get("d0.lean.accept") == c.get("d0.cases") == c.get("d0.python.accept")
      and c.get("mutants.lean.reject", 0) == c.get("mutants.cases", 0) == c.get("mutants.python.reject", 0))
print(f"d0 {c.get('d0.cases')} accepted by Lean/Python, mutants {c.get('mutants.cases', 0)} rejected, {r['disagreements']} disagreements")
sys.exit(0 if ok else 1)
PY
); then pass "extra acceptance: $r"
  else bad "extra acceptance: ${r:-difftest failed}"; head -3 "$xo/difftest.err"; fi
else bad "extra acceptance: $chk not built (lake build nearspec-v3-check-d0a in zk-formal)"; fi

echo "== extra D0a fixtures: prepared statement, real-witness tables, SHA bins, srcp bus"
nx=0
for d in "$xf"/d0/*; do
  [ -f "$d/witness.bin" ] || continue
  c=$(basename "$d"); o="$xo/$c"; mkdir -p "$o"; nx=$((nx + 1))
  # --- prepared statement -----------------------------------------------------------------
  if ! $HEAVY "$lp" "$d" "$o" 2>"$o/prep.err"; then bad "$c: np-lean-prep-v3 failed"; head -3 "$o/prep.err"; continue; fi
  python3 - "$o" <<'PY'
import json, sys
o = sys.argv[1]; d = json.load(open(o + "/prep.json"))
for k, f in (("public", "lean.pub"), ("prep", "lean.prep"), ("hint", "lean.hint")):
    open(f"{o}/{f}", "wb").write(bytes.fromhex(d[k]))
json.dump(d["prep_json"], open(o + "/pj.json", "w"))
PY
  "$npudr" v3public "$o/pj.json" "$o/rust.pub" >/dev/null 2>&1 && cmp -s "$o/lean.pub" "$o/rust.pub" \
    && pass "$c public tape byte-identical ($(stat -c %s "$o/rust.pub") B)" || bad "$c public tape differs"
  "$npudr" prep-encode "$o/prep.json" "$o/rust.prep" 2>/dev/null && cmp -s "$o/lean.prep" "$o/rust.prep" \
    && pass "$c Prep.encode byte-identical" || bad "$c Prep.encode differs"
  "$npudr" prep-hint "$o/lean.hint" "$o/hint.rt" 2>/dev/null && cmp -s "$o/lean.hint" "$o/hint.rt" \
    && pass "$c Hint codec round-trips" || bad "$c Hint codec"
  if "$npudr" d0-prep "$d/claim.bin" "$o/lean.hint" "$o/d0.json" >/dev/null 2>"$o/d0.err" && \
     "$npudr" prep-encode "$o/d0.json" "$o/d0.prep" 2>/dev/null && cmp -s "$o/d0.prep" "$o/lean.prep"; then
    pass "$c d0-prep (prepClaim/prepBody) == Lean prepD0"
  else bad "$c d0-prep differs"; head -2 "$o/d0.err"; fi
  if "$npudr" v3prepare "$d/claim.bin" "$d/witness.bin" "$o/vp" >/dev/null 2>&1 && \
     cmp -s "$o/vp/hint.bin" "$o/lean.hint" && cmp -s "$o/vp/prep.bin" "$o/lean.prep"; then
    pass "$c v3prepare (hintOf + prepD0) == Lean"
  else bad "$c v3prepare differs ($(head -c 120 "$o/vp/reject.txt" 2>/dev/null))"; fi
  if r=$(python3 - "$o/pj.json" "$o/rust.pub" <<'PY'
import json, sys, collections
pj = json.load(open(sys.argv[1])); tape = open(sys.argv[2], "rb").read()
ls = pj["lists"]; keys = [tuple(l["key"]) for l in ls]; cnt = collections.Counter(keys)
# Public.sourceDupByte / sourceRep (Public/Source.lean), recomputed independently
def dupb(j):
    prev = [i for i in range(j) if keys[i] == keys[j]]
    if not prev: return 0
    ok = all(ls[i]["fromShard"] == ls[j]["fromShard"] and ls[i]["root"] == ls[j]["root"] for i in prev)
    return 1 if ok else 2
rows = [bytes([dupb(j), int(cnt[keys[j]] > 1)]) + bytes(ls[j]["root"]) for j in range(len(ls))]
blob = b"".join(rows)
ok = blob in tape
print(f"{len(ls)} source rows, dup1 {sum(r[0] == 1 for r in rows)}, rep {sum(r[1] for r in rows)}")
sys.exit(0 if ok else 1)
PY
  ); then pass "$c source rows [dup, rep] = sourceDupByte/sourceRep ($r)"
  else bad "$c source rows differ from sourceDupByte/sourceRep ($r)"; fi
  # --- real-witness entries: node / val / head ---------------------------------------------
  for t in node val head; do
    j="$o/$t.json"
    if ! $HEAVY "$le3" "$d" $t > "$j" 2>"$j.err"; then bad "$c $t: np-lean-entries-v3 failed"; head -3 "$j.err"; continue; fi
    nr=$(python3 -c "import json;print(len(json.load(open('$j'))))")
    if ! "$npudr" v3check "$air" $t "$j" >"$j.check" 2>&1; then bad "$c $t: v3check rejects honest entries"; head -3 "$j.check"; continue; fi
    case $t in
      node) if [ "$nr" -le "${EXTRA_NODE_MAX:-0}" ]; then rl="$la7"; else pass "$c $t: $(cut -c5- "$j.check") ($nr records; Lean render skipped)"; continue; fi ;;
      val) rl="$la7" ;;
      head) rl="$lr" ;;
    esac
    "$npudr" v3render $t "$j" "$j.rust.bin" && $HEAVY "$rl" $t "$j" "$j.lean.bin" 2>"$j.lerr" && cmp -s "$j.rust.bin" "$j.lean.bin" \
      && pass "$c $t: $(cut -c5- "$j.check"); Rust == Lean ($nr entries$( [ $t = val ] && echo ", $(python3 -c "import json;print(sum(1 for e in json.load(open('$j')) if not e['bytes']))") empty"))" \
      || bad "$c $t: Rust and Lean traces differ"
    rm -f "$j.rust.bin" "$j.lean.bin"
  done
  # --- SHA bins (tables 0/1), srcp (20), acct (17) -------------------------------------------
  if ! $HEAVY "$lsb" "$d" > "$o/sb.json" 2>"$o/sb.err"; then bad "$c: np-lean-shabins-v3 failed"; head -3 "$o/sb.err"; continue; fi
  ed="$o/ent"; mkdir -p "$ed"
  python3 - "$o/sb.json" "$ed" "$o/pj.json" <<'PY'
import json, sys, os, collections
d = json.load(open(sys.argv[1])); ed = sys.argv[2]; pj = json.load(open(sys.argv[3]))
for t, v in d["entries"].items():
    json.dump(v, open(os.path.join(ed, t + ".json"), "w"))
json.dump(d["receipt"], open(os.path.join(ed, "sha_receipt.json"), "w"))
keys = [tuple(l["key"]) for l in pj["lists"]]; cnt = collections.Counter(keys)
s = d["entries"]["srcp"]
for e in s: e["rep"] = cnt[keys[e["j"]]] > 1      # sourceRep (the bus-14 check below binds it to the tape)
json.dump(s, open(os.path.join(os.path.dirname(ed), "srcp.json"), "w"))
PY
  if "$npudr" v3sha "$ed" "$o/sha_t.json" "$o/sha_r.json" "$o/rust.json" 2>"$o/v3sha.err" && \
     r=$(python3 - "$o/sb.json" "$o/rust.json" <<'PY'
import json, sys
L = json.load(open(sys.argv[1])); R = json.load(open(sys.argv[2]))
key = lambda ms: [(m["id"], list(m["bytes"]), bool(m["dmult"])) for m in ms]
bad = [f for f in ("scheduler", "native", "receipt", "source", "b0", "b1") if key(L[f]) != key(R[f])]
if L["cap"] != R["cap"]: bad.append("cap")
ez = sum(1 for m in R["native"] if not m["bytes"])
rc = [m for m in R["receipt"] if m["id"] % 16 == 1]
print(f"{ez} zero-length VPRE jobs, {len(rc)} RC jobs ({sum(not m['dmult'] for m in rc)} gated)", " ".join(bad))
sys.exit(1 if bad else 0)
PY
  ); then pass "$c SHA families + bins identical ($r)"
  else bad "$c SHA families/bins differ (${r:-v3sha failed: $(tail -1 "$o/v3sha.err")})"; fi
  for tb in sha_t sha_r; do
    "$npudr" v3check "$air" $tb "$o/$tb.json" >"$o/$tb.check" 2>&1 && pass "$c $tb: $(cut -c5- "$o/$tb.check")" \
      || { bad "$c $tb: constraints fail"; head -3 "$o/$tb.check"; }
  done
  for t in srcp acct; do
    j="$o/$t.json"; [ $t = acct ] && j="$ed/acct.json"
    "$npudr" v3check "$air" $t "$j" >"$j.check" 2>&1 || { bad "$c $t: v3check rejects honest entries"; head -3 "$j.check"; continue; }
    "$npudr" v3render $t "$j" "$j.rust.bin" && $HEAVY "$lrr" $t "$j" "$j.lean.bin" 2>/dev/null && cmp -s "$j.rust.bin" "$j.lean.bin" \
      && pass "$c $t: $(cut -c5- "$j.check"); Rust == Lean" || bad "$c $t: Rust and Lean traces differ"
    rm -f "$j.rust.bin" "$j.lean.bin"
  done
  "$npudr" v3bus "$air" "$o/lean.pub" 14 srcp="$o/srcp.json" >"$o/bus.out" 2>&1 \
    && pass "$c srcp bus 14 (B_SRC) balanced against the public tape" || { bad "$c srcp bus 14 unbalanced"; tail -2 "$o/bus.out"; }
  # --- negatives on repeated keys ---------------------------------------------------------
  for mut in fromshard root rep; do
    if ! python3 - "$o" "$mut" <<'PY'
import json, sys, collections
o, mut = sys.argv[1], sys.argv[2]
pj = json.load(open(o + "/pj.json")); s = json.load(open(o + "/srcp.json"))
keys = [tuple(l["key"]) for l in pj["lists"]]
dups = [j for j in range(len(keys)) if keys[j] in keys[:j]]
if not dups: sys.exit(3)
j = dups[-1]
if mut == "fromshard":   # same key, other from-shard: inconsistent repeat, root row unchanged
    pj["lists"][j]["fromShard"] += 1
elif mut == "root":      # same key, other root
    pj["lists"][j]["root"][0] ^= 1
else:                    # honest tape, srcp rep bit of a repeated block cleared
    e = next(e for e in s if e["j"] == j); e["rep"] = False
json.dump(pj, open(f"{o}/neg-{mut}.pj.json", "w")); json.dump(s, open(f"{o}/neg-{mut}.srcp.json", "w"))
PY
    then continue; fi
    if [ $mut = rep ]; then cp "$o/lean.pub" "$o/neg-$mut.pub"
    else
      "$npudr" v3public "$o/neg-$mut.pj.json" "$o/neg-$mut.pub" >/dev/null 2>&1 || { bad "$c neg $mut: v3public failed"; continue; }
      python3 - "$o/neg-$mut.pj.json" "$o/neg-$mut.pub" <<'PY' || { bad "$c neg $mut: tape has no dup byte 2 row"; continue; }
import json, sys
pj = json.load(open(sys.argv[1])); tape = open(sys.argv[2], "rb").read()
keys = [tuple(l["key"]) for l in pj["lists"]]
j = [j for j in range(len(keys)) if keys[j] in keys[:j]][-1]
sys.exit(0 if bytes([2, 1]) + bytes(pj["lists"][j]["root"]) in tape else 1)
PY
    fi
    if "$npudr" v3bus "$air" "$o/neg-$mut.pub" 14 srcp="$o/neg-$mut.srcp.json" >"$o/neg-$mut.bus" 2>&1; then
      bad "$c neg $mut: bus 14 still balanced"
    else pass "$c neg $mut: $( [ $mut = rep ] && echo "rep bit cleared" || echo "dup byte 2 row") -> bus 14 unbalanced ($(tail -1 "$o/neg-$mut.bus" | cut -c6-))"; fi
  done
done
[ $nx -gt 0 ] || bad "extra: no fixture in $xf/d0"
echo "   ($nx extra fixtures)"
