# shellcheck shell=bash
# Section `rcs` (sourced by run-v2.sh / run-v2-section.sh; `here src out npudr HEAVY pass bad`
# in scope): nearAirV3 tables 20 `srcp` (SrcpDD.table), 17 `acct` (acctTableV3), 23 `mrk`
# (MerkleEmpty.table) and 24 `sort` (sortTableV3).
#
# 1. Rust `npudr v3render` vs the Lean honest renders `np-lean-render-v3-rcs`
#    (srcpDDTrace / acctTraceAlignedE / mrkTraceV3 / sortTraceV3) on seeded honest entries
#    (`npudr v3sample`), sizes incl. 0: byte-identical dumps.
# 2. `npudr v3check` (every constraint of the nearAirV3 table; mrk with the honest PH_N count).
# 3. Entries outside the honest-input predicate must violate a constraint.
#
# Knobs: RCS_SEEDS (default "1 2 3"), RCS_SIZES (default "0 1 5 12"), RCS_MRK_SIZES
# (default "0 1 2 5 9"; every mrk dump is 2^19 x 60 cells, removed after the comparison).
lrr="$here/.lake/build/bin/np-lean-render-v3-rcs"
rcs="$out/rcs"; mkdir -p "$rcs"
air="$out/nearAirV3.json"

# mrk public prefix: PH_N = 30..33 the little-endian count (`MerkleEmpty.countE`), PH_OUT
# (146..177) zero; `rcs_mrkpub <entries.json> [count override] [PH_OUT byte 0]`.
rcs_mrkpub() {
  python3 - "$@" <<'PY'
import json, sys
n = json.load(open(sys.argv[1]))['n']
if len(sys.argv) > 2: n = int(sys.argv[2])
p = [0] * 178
for i in range(4): p[30 + i] = (n >> (8 * i)) & 255
if len(sys.argv) > 3: p[146] = int(sys.argv[3])
print(json.dumps(p))
PY
}

rcs_check() { # rcs_check <table> <entries.json> <label> [pubs.json]
  local f="${2%.json}"
  if "$npudr" v3check "$air" "$1" "$2" ${4:+"$4"} >"$f.check" 2>&1; then pass "$3 $(cut -c5- "$f.check")"
  else bad "$3 constraints fail"; head -3 "$f.check"; fi
}

rcs_diff() { # rcs_diff <table> <entries.json> <label> -> 0 iff identical
  local t=$1 f="${2%.json}" s0 s1 rc=0
  s0=$(date +%s.%N)
  if ! $HEAVY "$lrr" "$t" "$2" "$f.lean.bin" 2>"$f.err"; then bad "$3: np-lean-render-v3-rcs failed"; head -3 "$f.err"; return 1; fi
  s1=$(date +%s.%N)
  if ! "$npudr" v3render "$t" "$2" "$f.rust.bin"; then bad "$3: npudr v3render failed"; return 1; fi
  if cmp -s "$f.lean.bin" "$f.rust.bin"; then
    pass "$3 trace identical ($(stat -c %s "$f.rust.bin") B, sha256 $(sha256sum "$f.rust.bin" | cut -c1-16), lean $(printf '%.1f' "$(echo "$s1 - $s0" | bc)")s)"
  else bad "$3 trace differs"; rc=1; fi
  [ "$t" = mrk ] && rm -f "$f.lean.bin" "$f.rust.bin"
  return $rc
}

for t in srcp acct sort mrk; do
  sizes="${RCS_SIZES:-0 1 5 12}"; [ "$t" = mrk ] && sizes="${RCS_MRK_SIZES:-0 1 2 5 9}"
  for seed in ${RCS_SEEDS:-1 2 3}; do
    for n in $sizes; do
      f="$rcs/$t-$seed-$n"
      "$npudr" v3sample $t $seed $n > "$f.json" || { bad "$t seed=$seed n=$n: v3sample failed"; continue; }
      rcs_diff $t "$f.json" "$t seed=$seed n=$n"
      if [ "$t" = mrk ]; then rcs_mrkpub "$f.json" > "$f.pub.json"; rcs_check mrk "$f.json" "$t seed=$seed n=$n" "$f.pub.json"
      elif [ "$t" = srcp ] && [ "$n" = 0 ]; then
        # no source occurrence is not an honest table-20 input (`DedupRender.TableFacts.nonempty`;
        # an accepted chunk has one, `relD0a_blocks_nonempty`): row 0 must be a root row
        if "$npudr" v3check "$air" srcp "$f.json" >"$f.check" 2>&1; then bad "srcp seed=$seed n=0: empty table admitted"
        else pass "srcp seed=$seed n=0: empty table rejected ($(head -1 "$f.check"), isFirst·(1 − rt))"; fi
      else rcs_check $t "$f.json" "$t seed=$seed n=$n"; fi
    done
  done
done

# srcp edge: a block at the A10 bound |path| = DP0 = 32 (depth slack 0), plus dup/rep blocks.
# `rcs_srcp_fix` recomputes the counters of `TableFacts` (j, ql/qe/le, item q/pq/pl) in order.
rcs_srcp_fix='
def fix(es):
    q = 1
    for j, e in enumerate(es):
        e["j"] = j; e["ql"] = q; d = len(e["path"])
        e["qe"] = q + d; e["le"] = 32 if d == 0 else 64
        for i, it in enumerate(e["path"]):
            it["q"] = q + 1 + i; it["pq"] = q + i; it["pl"] = 32 if i == 0 else 64
        if not e["dup"]: q += d + 1
    return es
def deep(es, k, d):
    it = es[k]["path"][0] if es[k]["path"] else {"dir": True, "sib": [7]*32, "acc": [9]*32}
    es[k]["path"] = [dict(it, dir=(i % 3 == 0), sib=[(i * 13 + b) % 256 for b in range(32)]) for i in range(d)]
    return fix(es)
'
rcs_srcp() { # rcs_srcp <seed> <n> <out.json> <python edit of `es`>
  "$npudr" v3sample srcp "$1" "$2" | python3 -c "import json,sys
$rcs_srcp_fix
es=json.load(sys.stdin)
$4
print(json.dumps(es))" > "$3"
}
f="$rcs/srcp-depth32"
rcs_srcp 3 4 "$f.json" "es = deep(es, 0, 32)"
rcs_diff srcp "$f.json" "srcp |path| = DP0 (32) with dup/rep blocks"
rcs_check srcp "$f.json" "srcp |path| = DP0 (32)"

# --- negatives: the rendered trace must violate a constraint --------------------------------
rcs_broken() { # rcs_broken <table> <label> <entries.json> [pubs.json]
  local f="${3%.json}"
  if "$npudr" v3check "$air" "$1" "$3" ${4:+"$4"} >"$f.check" 2>&1; then bad "$1 $2: constraints still hold"
  else pass "$1 $2: constraint violated ($(head -1 "$f.check"))"; fi
}
rcs_neg() { # rcs_neg <table> <seed> <n> <label> <python edit of `es`>
  local f="$rcs/broken-$1-$(echo "$4" | tr -c 'A-Za-z0-9' _)"
  if [ "$1" = srcp ]; then rcs_srcp "$2" "$3" "$f.json" "$5"
  else "$npudr" v3sample "$1" "$2" "$3" | python3 -c "import json,sys; es=json.load(sys.stdin); $5; print(json.dumps(es))" > "$f.json"; fi
  rcs_broken "$1" "$4" "$f.json"
}
# srcp (seed 3, n 6 has dup and rep blocks; `D`/`R`: first dup / first rep-not-dup block)
D="D = next(i for i, e in enumerate(es) if e['dup'])"
R="R = next(i for i, e in enumerate(es) if e['rep'] and not e['dup'])"
rcs_neg srcp 3 6 "depth DP0+1 = 33" "es = deep(es, 0, 33)"
rcs_neg srcp 3 6 "dup with L != 12" "$D; es[D]['L'] = 13"
rcs_neg srcp 3 6 "repeated first occurrence with L != 12" "$R; es[R]['L'] = 11"
rcs_neg srcp 3 6 "dup without rep" "$D; es[D]['rep'] = False"
rcs_neg srcp 3 6 "dup message counter not shared" "$D; es[D]['ql'] += 1"
rcs_neg srcp 3 6 "first path item pl != 32" "k = next(i for i, e in enumerate(es) if e['path'] and not e['dup']); es[k]['path'][0]['pl'] = 64"
# acct
rcs_neg acct 7 5 "pre amount is u128::MAX" "es[0]['pre'] = [255]*16 + es[0]['pre'][16:]"
rcs_neg acct 7 5 "pre amount byte 256 (dsum recurrence)" "es[0]['pre'][3] = 256"
# sort
rcs_neg sort 7 5 "ids not ascending" "es[1], es[2] = es[2], es[1]"
rcs_neg sort 7 5 "repeated id" "es[2] = [es[2][0], es[1][1]]"
# mrk (public count / root mismatches)
f="$rcs/broken-mrk"; "$npudr" v3sample mrk 7 5 > "$f.json"
rcs_mrkpub "$f.json" 6 > "$f.pub6.json";  rcs_broken mrk "public count 6 != 5 leaves" "$f.json" "$f.pub6.json"
rcs_mrkpub "$f.json" 0 > "$f.pub0.json";  rcs_broken mrk "public count 0 with 5 leaves" "$f.json" "$f.pub0.json"
f="$rcs/broken-mrk0"; "$npudr" v3sample mrk 7 0 > "$f.json"
rcs_mrkpub "$f.json" 1 > "$f.pub1.json";  rcs_broken mrk "empty tree with public count 1" "$f.json" "$f.pub1.json"
rcs_mrkpub "$f.json" 0 1 > "$f.pubo.json"; rcs_broken mrk "empty tree with nonzero root byte" "$f.json" "$f.pubo.json"
