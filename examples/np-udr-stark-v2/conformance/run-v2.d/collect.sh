# run-v2.d/collect.sh — the SHA job collector of nearAirV3 tables 0/1 (sourced by run-v2.sh /
# run-v2-section.sh collect; in scope: here src out npudr lr le le3 lp fx HEAVY pass bad).
#
# Ground truth: `np-lean-shabins-v3 <case>` (ShaBinsV3.lean) evaluates, for a real D0a fixture
# (`checkD0a B0` first), the four SHA job families of `TrieSide.trie_side_exact` (scheduler,
# native, receipt, source) and their two bins `TrieShaTwo.twoShaJobBins = [b0, b1]`, and dumps
# the honest per-table entries they come from (node, val, acct, srcp; ups/codec reduced to the
# fields the collector reads).  `npudr v3sha` rebuilds the families and bins from those entry
# files; every family list and both bins must be identical (order, id, bytes, dmult), and the
# collector's bus check (the supplied tables' BYTES sends / DIGEST receives against the bins'
# expected bytes / digests) must pass.  The receipt family needs the `rcpt` entries (receipt
# list views), which no real-witness dumper produces yet: it is supplied as `sha_receipt.json`
# (the Lean family) for the bins, and its account part is checked separately from `acct`.
#
# Knobs: COLLECT_CASES (all fixtures), COLLECT_CHECK (2: v3check of sha_t/sha_r on the first
# cases), COLLECT_NEG (3: negative cases).
cdir="$out/collect"; mkdir -p "$cdir"
lsb="$here/.lake/build/bin/np-lean-shabins-v3"
air="$out/nearAirV3.json"
echo "== SHA job bins (tables 0/1): npudr v3sha vs np-lean-shabins-v3 (real fixtures)"
ncase=0; nfail=0; nchk=0; nneg=0
declare -A famok=([scheduler]=0 [native]=0 [receipt]=0 [source]=0 [account]=0 [bins]=0)
for case in $(ls "$fx" | head -${COLLECT_CASES:-1000}); do
  d="$fx/$case"; [ -f "$d/witness.bin" ] || continue
  lj="$cdir/$case.lean.json"; ed="$cdir/$case.ent"; mkdir -p "$ed"
  if ! $HEAVY "$lsb" "$d" > "$lj" 2>"$lj.err"; then bad "$case: np-lean-shabins-v3 failed"; head -3 "$lj.err"; nfail=$((nfail+1)); continue; fi
  python3 - "$lj" "$ed" <<'PY'
import json, sys, os
d = json.load(open(sys.argv[1])); ed = sys.argv[2]
for t, v in d["entries"].items():
    json.dump(v, open(os.path.join(ed, t + ".json"), "w"))
json.dump(d["receipt"], open(os.path.join(ed, "sha_receipt.json"), "w"))
PY
  rj="$cdir/$case.rust.json"
  if ! "$npudr" v3sha "$ed" "$cdir/$case.sha_t.json" "$cdir/$case.sha_r.json" "$rj" 2>"$cdir/$case.v3sha.err"; then
    bad "$case: npudr v3sha failed"; tail -3 "$cdir/$case.v3sha.err"; nfail=$((nfail+1)); continue
  fi
  # account part of the receipt family from the acct entries alone (no sha_receipt.json)
  ea="$cdir/$case.ent-acct"; mkdir -p "$ea"; cp -f "$ed/acct.json" "$ea/acct.json"
  "$npudr" v3sha "$ea" "$ea/t.json" "$ea/r.json" "$ea/full.json" 2>"$ea/err" >/dev/null
  if res=$(python3 - "$lj" "$rj" "$cdir/$case.sha_t.json" "$cdir/$case.sha_r.json" "$ea/full.json" <<'PY'
import json, sys
L = json.load(open(sys.argv[1])); R = json.load(open(sys.argv[2]))
t = json.load(open(sys.argv[3])); r = json.load(open(sys.argv[4])); A = json.load(open(sys.argv[5]))
key = lambda ms: [(m["id"], list(m["bytes"]), bool(m["dmult"])) for m in ms]
ok = {}
for f in ("scheduler", "native", "receipt", "source"):
    ok[f] = key(L[f]) == key(R[f])
ok["account"] = key([m for m in L["receipt"] if m["id"] % 16 == 10]) == key(A["receipt"])
ok["bins"] = key(L["b0"]) == key(R["b0"]) == key(t) and key(L["b1"]) == key(R["b1"]) == key(r) \
    and L["cap"] == R["cap"]
bus = R["bus"]
n = {f: len(L[f]) for f in ("scheduler", "native", "receipt", "source", "b0", "b1")}
print(" ".join(f for f, v in ok.items() if v), "|",
      " ".join(f"{k}={v}" for k, v in n.items()),
      f"cap={L['cap']} bus: {bus['sends']} sends, {bus['recvs']} recvs ok, {bus['unsent']} bytes / {bus['unreceived']} digests from unsupplied tables",
      "|", " ".join(f for f, v in ok.items() if not v))
sys.exit(0 if all(ok.values()) else 1)
PY
  ); then
    pass "$case: families + bins identical; ${res#*| }"
  else
    bad "$case: differs in [${res##*| }] (${res#*| })"; nfail=$((nfail+1))
  fi
  for f in ${res%%|*}; do famok[$f]=$((famok[$f]+1)); done
  ncase=$((ncase+1))
  # every constraint of the two SHA tables on the collected bins (first cases)
  if [ $nchk -lt ${COLLECT_CHECK:-2} ]; then
    for tb in sha_t sha_r; do
      if "$npudr" v3check "$air" $tb "$cdir/$case.$tb.json" >"$cdir/$case.$tb.check" 2>&1; then
        pass "$case $tb: $(cut -c5- "$cdir/$case.$tb.check")"
      else bad "$case $tb: constraints fail"; head -3 "$cdir/$case.$tb.check"; fi
    done
    nchk=$((nchk+1))
  fi
  # negatives: broken entries must make the bus check fail
  if [ $nneg -lt ${COLLECT_NEG:-3} ]; then
    nneg=$((nneg+1))
    for mut in val-byte rc-missing srcp-leaf; do
      nd="$cdir/$case.neg-$mut"; rm -rf "$nd"; cp -r "$ed" "$nd"
      if ! python3 - "$nd" "$mut" <<'PY'
import json, sys, os
nd, mut = sys.argv[1], sys.argv[2]
ld = lambda t: json.load(open(os.path.join(nd, t + ".json")))
sv = lambda t, v: json.dump(v, open(os.path.join(nd, t + ".json"), "w"))
if mut == "val-byte":          # a non-empty value's byte: its VPRE digest no longer matches the node slot
    vs = ld("val"); e = next((e for e in vs if e["bytes"]), None)
    if e is None: sys.exit(3)
    e["bytes"][0] = (e["bytes"][0] + 1) % 256; sv("val", vs)
elif mut == "rc-missing":      # drop the RC jobs: the source table's RC(j) digest receives are unanswered
    rs = [m for m in ld("sha_receipt") if m["id"] % 16 != 1]
    if len(rs) == len(ld("sha_receipt")): sys.exit(3)
    sv("sha_receipt", rs)
elif mut == "srcp-leaf":       # a source leaf byte: its RC(j) digest receive no longer matches
    bs = ld("srcp"); b = next((b for b in bs if not b["dup"]), None)
    if b is None: sys.exit(3)
    b["leaf"][0] = (b["leaf"][0] + 1) % 256; sv("srcp", bs)
PY
      then continue; fi
      if "$npudr" v3sha "$nd" "$nd/t.json" "$nd/r.json" 2>"$nd/err"; then bad "$case neg $mut: bus check still passes"
      else pass "$case neg $mut: rejected ($(grep -o '[0-9]* receives ([0-9]* unmatched)' "$nd/err" | head -1))"; fi
    done
  fi
done
[ $ncase -gt 0 ] || bad "collect: no fixture produced SHA bins"
echo "   ($ncase fixtures; identical: scheduler ${famok[scheduler]}, native ${famok[native]}, receipt ${famok[receipt]} (Lean-supplied), account part ${famok[account]}, source ${famok[source]}, bins ${famok[bins]}; $nfail failures)"
