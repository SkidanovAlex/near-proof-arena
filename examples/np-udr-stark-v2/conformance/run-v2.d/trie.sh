# shellcheck shell=bash
# run-v2.d/trie.sh — the trie side of nearAirV3 on HONEST real-witness entries (sourced by
# run-v2.sh / run-v2-section.sh trie; in scope: here src out npudr lr le le3 lp fx HEAVY pass bad).
#
# Ground truth: `np-lean-trie-v3 <case>` (TrieEntriesV3.lean) evaluates the entry lists of
# `Assembly/TrieSide.lean` `trie_side_exact` on the native objects of the accepted witness:
# node (2, + A7 `rpl`), head (3), val (4, + A7 `rpl`), walk (5), uniq (6), ups (7, honest
# native instances), size (21, `[{x0,x1,x2,ovh,yN}]`).  For every fixture (the 64 public D0a
# cases + the extra cases with repeated source keys / empty values):
#
# 1. Lean dump accepted (its self-checks: rpl/rplv singletons distinct, A7 total ≤ B0, …);
# 2. Rust derivation `npudr v3trie <case>` (claim + witness → entries, `src/v3/trie.rs`) equals
#    the Lean entries, table by table; and the native stage `npudr v3native` equals the Lean
#    `native` dump (tries, account replay, scheduler upsert runs);
# 3. `npudr v3check`: every nearAirV3 constraint of the 7 rendered tables holds;
# 4. Rust render (`npudr v3render`) == Lean render (`np-lean-render-v3-a7` for node/val/ups/size,
#    `np-lean-render-v3` for head/walk/uniq), compared by sha256;
# 5. bus balance of the trie tables against the case's public tape (`npudr v3bus`): PARENT 2,
#    EDGE 4, ROOT 10, BMAP 11, DIGS 17, DUP 19, ENT 20, VPARENT 22, MEMD 23, MIDROOT 24, UPB 25,
#    RPL 70, RPLV 71 (the buses `trie_side_exact` balances from the trie tables alone);
# 6. negatives (TRIE_NEG_CASES cases): single-entry mutations of the honest entries must break
#    a constraint or one of these buses (value-byte mutations are caught on BYTES/VBYTES with
#    the SHA/codec tables, outside this section).
#
# Knobs: TRIE_FX (fixture dirs, default "$fx $here/fixtures-extra/d0"), TRIE_MAX (cases per
# dir, default all), TRIE_NEG_CASES (3), TRIE_RENDER (1: run step 4), TRIE_RUST (1: run step 2).
to="$out/trie"; rm -rf "$to"; mkdir -p "$to"
ltr="$here/.lake/build/bin/np-lean-trie-v3"
la7="$here/.lake/build/bin/np-lean-render-v3-a7"
air="$out/nearAirV3.json"
TT="node val head walk uniq ups size"
TB="2 4 10 11 17 19 20 22 23 24 25 70 71"

# split <json> <prefix>: one file per table
tsplit() {
  python3 - "$1" "$2" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
for t in ["node", "val", "head", "walk", "uniq", "ups", "size"]:
    json.dump(d[t], open(f"{sys.argv[2]}.{t}.json", "w"))
PY
}
# tsame <a.json> <b.json>: same tables (and same checks), prints the differing tables
tsame() {
  python3 - "$1" "$2" <<'PY'
import json, sys
a = json.load(open(sys.argv[1])); b = json.load(open(sys.argv[2]))
bad = [k for k in ["node", "val", "head", "walk", "uniq", "ups", "size", "checks"] if a.get(k) != b.get(k)]
print(" ".join(bad)); sys.exit(1 if bad else 0)
PY
}
# nsame <lean native.json> <rust native.json>: the native keys Rust emits agree
nsame() {
  python3 - "$1" "$2" <<'PY'
import json, sys
a = json.load(open(sys.argv[1])); b = json.load(open(sys.argv[2]))
bad = [k for k in b if a.get(k) != b[k]]
print(" ".join(bad)); sys.exit(1 if bad or not b else 0)
PY
}
# tbus <case-prefix> <tape> <bus>
tbus() {
  local p=$1 tape=$2 b=$3
  "$npudr" v3bus "$air" "$tape" "$b" node="$p.node.json" head="$p.head.json" val="$p.val.json" \
    walk="$p.walk.json" uniq="$p.uniq.json" ups="$p.ups.json" size="$p.size.json" > "$p.bus$b" 2>&1
}

ncase=0; nrust=0; ntab=0; nren=0; nbus=0
for dir in ${TRIE_FX:-$fx $here/fixtures-extra/d0}; do
  for case in $(ls "$dir" | head -"${TRIE_MAX:-1000}"); do
    d="$dir/$case"; [ -f "$d/witness.bin" ] || continue
    p="$to/$case"
    if ! $HEAVY "$ltr" "$d" > "$p.lean.json" 2> "$p.lean.err"; then
      bad "$case: np-lean-trie-v3 failed ($(head -c 200 "$p.lean.err"))"; continue
    fi
    ncase=$((ncase + 1))
    tsplit "$p.lean.json" "$p"
    sz=$(python3 -c "import json;d=json.load(open('$p.lean.json'));print('node %d val %d head %d walk %d uniq %d ups %d yN %s' % (len(d['node']),len(d['val']),len(d['head']),len(d['walk']),len(d['uniq']),len(d['ups']),d['size'][0]['yN']))")
    # 2. Rust derivation
    if [ "${TRIE_RUST:-1}" = 1 ]; then
      if "$npudr" v3trie "$d" > "$p.rust.json" 2> "$p.rust.err" && r=$(tsame "$p.lean.json" "$p.rust.json"); then
        nrust=$((nrust + 1))
      else bad "$case: Rust v3trie != Lean entries (${r:-$(head -c 160 "$p.rust.err")})"; fi
      $HEAVY "$ltr" "$d" native > "$p.lnat.json" 2>/dev/null
      if "$npudr" v3native "$d" > "$p.rnat.json" 2> "$p.rnat.err" && r=$(nsame "$p.lnat.json" "$p.rnat.json"); then :
      else bad "$case: Rust v3native != Lean native (${r:-$(head -c 160 "$p.rnat.err")})"; fi
      rm -f "$p.lnat.json" "$p.rnat.json"
    fi
    # 3. constraints
    tok=1
    for t in $TT; do
      "$npudr" v3check "$air" $t "$p.$t.json" > "$p.$t.check" 2>&1 || { tok=0; bad "$case $t: v3check fails: $(head -1 "$p.$t.check")"; }
    done
    [ $tok = 1 ] && ntab=$((ntab + 1))
    # 4. Rust == Lean renders
    if [ "${TRIE_RENDER:-1}" = 1 ]; then
      rok=1
      for t in $TT; do
        case $t in node|val|ups|size) ex="$la7";; *) ex="$lr";; esac
        if $HEAVY "$ex" $t "$p.$t.json" "$p.$t.lean.bin" 2>"$p.$t.lerr" && "$npudr" v3render $t "$p.$t.json" "$p.$t.rust.bin" 2>"$p.$t.rerr" \
           && [ "$(sha256sum < "$p.$t.lean.bin")" = "$(sha256sum < "$p.$t.rust.bin")" ]; then :
        else rok=0; bad "$case $t: Rust and Lean renders differ ($(head -c 120 "$p.$t.lerr" "$p.$t.rerr" 2>/dev/null))"; fi
        rm -f "$p.$t.lean.bin" "$p.$t.rust.bin"
      done
      [ $rok = 1 ] && nren=$((nren + 1))
    fi
    # 5. buses against the public tape
    "$npudr" v3prepare "$d/claim.bin" "$d/witness.bin" "$p.prep" > /dev/null 2>&1 \
      && "$npudr" v3public "$p.prep/prep.json" "$p.tape" > /dev/null 2>&1 || { bad "$case: no public tape"; continue; }
    bok=1
    for b in $TB; do tbus "$p" "$p.tape" $b || { bok=0; bad "$case: bus $b unbalanced: $(tail -1 "$p.bus$b")"; }; done
    [ $bok = 1 ] && nbus=$((nbus + 1))
    [ $tok = 1 ] && [ $bok = 1 ] && pass "$case: honest trie side ($sz): 7 tables v3check, 13 buses balanced"
  done
done
[ $ncase -gt 0 ] || bad "trie: no fixture dumped"
echo "   ($ncase cases: Rust derivation == Lean $nrust, v3check $ntab, renders identical $nren, buses $nbus)"
[ "${TRIE_RUST:-1}" = 1 ] && [ $nrust = $ncase ] && pass "Rust v3trie == np-lean-trie-v3 on all $ncase cases"
[ "${TRIE_RENDER:-1}" = 1 ] && [ $nren = $ncase ] && pass "Rust == Lean renders (7 tables) on all $ncase cases"

echo "== trie: negatives (mutated honest entries must break a constraint or a bus)"
# neg <case-prefix> <tape> <label> <python mutation of d (dict of tables)> <check: table|bus:N>
neg() {
  local p=$1 tape=$2 lbl=$3 py=$4 chk=$5 q="$1.neg"
  python3 - "$p" "$q" "$py" <<'PY'
import json, sys
p, q, py = sys.argv[1:4]
d = {t: json.load(open(f"{p}.{t}.json")) for t in ["node", "val", "head", "walk", "uniq", "ups", "size"]}
exec(py)
for t, v in d.items(): json.dump(v, open(f"{q}.{t}.json", "w"))
PY
  case $chk in
    bus:*) if tbus "$q" "$tape" "${chk#bus:}"; then bad "$lbl: bus ${chk#bus:} still balanced"
           else pass "$lbl: bus ${chk#bus:} unbalanced ($(tail -1 "$q.bus${chk#bus:}" | cut -c1-60))"; fi ;;
    *) if "$npudr" v3check "$air" $chk "$q.$chk.json" > "$q.chk" 2>&1; then bad "$lbl: $chk constraints still hold"
       else pass "$lbl: $chk constraint violated ($(head -1 "$q.chk" | cut -c1-70))"; fi ;;
  esac
}
nn=0
for case in $(ls "$to" | sed -n 's/\.tape$//p' | head -"${TRIE_NEG_CASES:-3}"); do
  p="$to/$case"; t="$p.tape"
  neg "$p" "$t" "$case: rpl flag of a replaced node cleared" "i=[k for k,e in enumerate(d['node']) if e['rpl']][0]; d['node'][i]['rpl']=False" bus:70
  neg "$p" "$t" "$case: rpl flag of a val cleared" "i=[k for k,e in enumerate(d['val']) if e['rpl']][0]; d['val'][i]['rpl']=False" bus:71
  neg "$p" "$t" "$case: ups mid root changed" "d['ups'][0]['mid'][0]^=1" bus:24
  neg "$p" "$t" "$case: ups root part memory changed" "d['ups'][0]['parts'][-1]['mB']+=1" bus:23
  neg "$p" "$t" "$case: ups post root changed" "d['ups'][0]['post'][0]^=1" bus:10
  neg "$p" "$t" "$case: last walk dropped" "d['walk'].pop()" bus:4
  neg "$p" "$t" "$case: node use count +1" "d['node'][0]['uses'][0]+=1" bus:4
  neg "$p" "$t" "$case: uniq entry bytes changed" "d['uniq'][0]['bytes'][0]^=1" bus:17
  neg "$p" "$t" "$case: head pre root changed" "d['head'][0]['pre'][0]^=1" bus:10
  neg "$p" "$t" "$case: val id changed" "d['val'][0]['vid']+=1" bus:22
  neg "$p" "$t" "$case: A7 totals over B0" "d['size'][0]['yN']=[1999999,1,1]" size
  nn=$((nn + 1))
done
[ $nn -gt 0 ] || bad "trie: no negative case ran"
