# shellcheck shell=bash
# run-v2.d/schedqv.sh — nearAirV3 tables 8 chacha, 9 rng, 10 shuf, 11 codec, 12 scandist, 13 proc,
# 14 mem, 15 cmp and 22 qv on HONEST real-witness entries (sourced by run-v2.sh /
# run-v2-section.sh schedqv; in scope: here src out npudr fx HEAVY pass bad).
#
# Ground truth: `np-lean-sched-v3 <case> <dir>` (SchedEntriesV3.lean) evaluates the `PriorCore`
# block construction of the completeness proof (`native_allocated_blocks_run`: one block per
# scheduler call, `ActualRun.run`, `distributeEv` grants, `nativePriorIds`, `fwdLinks`) and the
# native qv walks/records (`qvNativeWalks`/`qvNativeRecords`).  For every fixture (64 public D0a +
# fixtures-extra):
#
# 1. the Lean dump is accepted (its self-checks: canonical prior-state view, grants = distRows);
# 2. `npudr v3sched <case>` (claim + witness → entries, `src/v3/schedqv.rs`) == the Lean entries,
#    file by file (JSON-equal);
# 3. `npudr v3check` of the 9 rendered tables (Rust entries, the case's public values);
# 4. Rust render (`npudr v3render`) == the Lean render of the native blocks with the proof's trace
#    definitions (`np-lean-sched-v3 render`, twins `codec_twin` … `qv_twin`), by sha256: the full
#    2^22 dumps of tables 11–15 for every case with >1 block or a bandwidth request (SCHEDQV_FULL=1:
#    every case), else the first SCHEDQV_PREFIX_ROWS rows (all non-padding rows); 8–10, 22 full;
# 5. bus balance against the case's public tape (`npudr v3bus`), every bus that touches tables
#    8–15/22, with the trie entries (`npudr v3trie`: ups, val, walk) and the receipt entries
#    (`npudr v3rcptfam`: rcpt, acct, akey) as the other participants: SCMP 40, SOP 41, SFIN 42,
#    SINC 43, SPUSH 44, SSIN 45, SSOUT 46, SSMEM 47, SGEN 48, SSHUF 49, SCHACHA 50, SPUBB 51,
#    SPAR 52, SDL 56, SDLX 57, SDG 58, S0F 59, SPOST 60, SPLEN 61, SA0 62, VSLOT 21, 29, 63, 5, 6.
#
# Then: the Lean scheduler sampler (`np-lean-render-v3-sched sample`, `ActualRun.run` with requests
# and rounds) against `npudr v3sched --rerun` (the Rust run re-derived from the block inputs), and
# the internal scheduler/ChaCha buses on the sampled blocks; negatives (mutated entries break a bus,
# a wrong witness is rejected).
#
# Knobs: SCHEDQV_FX (fixture dirs, default "$fx $here/fixtures-extra/d0"), SCHEDQV_MAX (cases per
# dir), SCHEDQV_FULL (0), SCHEDQV_PREFIX_ROWS (4096), SCHEDQV_RENDER (1), SCHEDQV_RCPT (1: buses
# 5/6 with the 2^22 rcpt render), SCHEDQV_NEG_CASES (3), SCHEDQV_SEEDS ("1 2 3").
so="$out/schedqv"; rm -rf "$so"; mkdir -p "$so"
lsq="$here/.lake/build/bin/np-lean-sched-v3"
lss="$here/.lake/build/bin/np-lean-render-v3-sched"
air="$out/nearAirV3.json"
ST="codec scandist proc mem cmp"
TT="chacha rng shuf codec scandist proc mem cmp qv"
BUS_A="40,41,42,43,44,45,46,47,48,49,50,51,52,56,57,58,59,60,61,62,21,29,63"
BUS_B="5,6"
prefix=${SCHEDQV_PREFIX_ROWS:-4096}

# ssame <lean dir> <rust dir>: JSON-equal entry files; prints the first difference
ssame() {
  python3 - "$1" "$2" <<'PY'
import json, os, sys
L, R = sys.argv[1:3]
def fd(a, b, p=''):
    if type(a) != type(b): return f'{p}: {str(a)[:60]} vs {str(b)[:60]}'
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if a.get(k) != b.get(k): return fd(a.get(k), b.get(k), p + '.' + k)
    if isinstance(a, list):
        if len(a) != len(b): return f'{p}: len {len(a)} vs {len(b)}'
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y: return fd(x, y, f'{p}[{i}]')
    return f'{p}: {str(a)[:60]} vs {str(b)[:60]}'
bad = []
for t in ["codec", "scandist", "proc", "mem", "cmp", "chacha", "rng", "shuf", "qv"]:
    a = json.load(open(os.path.join(L, t + ".json"))); b = json.load(open(os.path.join(R, t + ".json")))
    if a != b: bad.append(t + fd(a, b))
print(" | ".join(bad)); sys.exit(1 if bad else 0)
PY
}
# sbus <entries dir> <case prefix> <buses> <out>: render once, check the listed buses
sbus() {
  local e=$1 p=$2 bs=$3 o=$4
  if [ "$bs" = "$BUS_B" ]; then
    "$npudr" v3bus "$air" "$p.tape" "$bs" qv="$e/qv.json" walk="$p.walk.json" rcpt="$p.rf/rcpt.json" > "$o" 2>&1
  elif [ "$bs" = "$BUS_A" ]; then
    "$npudr" v3bus "$air" "$p.tape" "$bs" codec="$e/codec.json" scandist="$e/scandist.json" proc="$e/proc.json" \
      mem="$e/mem.json" cmp="$e/cmp.json" chacha="$e/chacha.json" rng="$e/rng.json" shuf="$e/shuf.json" \
      qv="$e/qv.json" ups="$p.ups.json" val="$p.val.json" acct="$p.rf/acct.json" akey="$p.rf/akey.json" > "$o" 2>&1
  else # every participant
    "$npudr" v3bus "$air" "$p.tape" "$bs" codec="$e/codec.json" scandist="$e/scandist.json" proc="$e/proc.json" \
      mem="$e/mem.json" cmp="$e/cmp.json" chacha="$e/chacha.json" rng="$e/rng.json" shuf="$e/shuf.json" \
      qv="$e/qv.json" ups="$p.ups.json" val="$p.val.json" acct="$p.rf/acct.json" akey="$p.rf/akey.json" \
      walk="$p.walk.json" rcpt="$p.rf/rcpt.json" > "$o" 2>&1
  fi
}

echo "== schedqv: honest tables 8-15, 22 from claim + witness (npudr v3sched vs np-lean-sched-v3)"
ncase=0; nrust=0; ntab=0; nren=0; nfull=0; nbus=0
for dir in ${SCHEDQV_FX:-$fx $here/fixtures-extra/d0}; do
  for case in $(ls "$dir" | head -"${SCHEDQV_MAX:-1000}"); do
    d="$dir/$case"; [ -f "$d/witness.bin" ] || continue
    p="$so/$case"
    # 1. Lean ground truth
    if ! $HEAVY "$lsq" "$d" "$p.lean" > "$p.lean.log" 2>&1; then
      bad "$case: np-lean-sched-v3 failed ($(tail -c 200 "$p.lean.log"))"; continue
    fi
    ncase=$((ncase + 1))
    sz=$(python3 -c "import json;s=json.load(open('$p.lean/summary.json'));print('blocks %d, requests %s, rounds %s, qv %d walks / %d records' % (s['blocks'],s['requests'],s['rounds'],s['qv_walks'],s['qv_records']))")
    big=$(python3 -c "import json;s=json.load(open('$p.lean/summary.json'));print(1 if s['blocks']>1 or sum(s['requests'])>0 else 0)")
    # 2. Rust derivation
    if "$npudr" v3sched "$d" "$p.rust" > "$p.rust.log" 2>&1 && r=$(ssame "$p.lean" "$p.rust"); then
      nrust=$((nrust + 1))
    else bad "$case: Rust v3sched != Lean entries (${r:-$(tail -c 160 "$p.rust.log")})"; continue; fi
    # public tape and its public values
    "$npudr" v3prepare "$d/claim.bin" "$d/witness.bin" "$p.prep" > /dev/null 2>&1 \
      && "$npudr" v3public "$p.prep/prep.json" "$p.tape" > /dev/null 2>&1 || { bad "$case: no public tape"; continue; }
    np=$(python3 -c "import json;print(json.load(open('$air'))['numPub'])")
    python3 -c "import json;print(json.dumps(list(open('$p.tape','rb').read()[:$np])))" > "$p.pubs.json"
    # 3. constraints
    tok=1
    for t in $TT; do
      "$npudr" v3check "$air" $t "$p.rust/$t.json" "$p.pubs.json" > "$p.$t.check" 2>&1 \
        || { tok=0; bad "$case $t: v3check fails: $(head -1 "$p.$t.check")"; }
    done
    [ $tok = 1 ] && ntab=$((ntab + 1))
    # 4. Rust render == Lean native render
    if [ "${SCHEDQV_RENDER:-1}" = 1 ]; then
      rok=1
      full=$big; [ "${SCHEDQV_FULL:-0}" = 1 ] && full=1
      for t in $TT; do
        case " $ST " in
          *" $t "*) if [ $full = 1 ]; then
                      hl=$($HEAVY "$lsq" render $t "$d" - 2>"$p.$t.lerr" | sha256sum | cut -c1-64)
                      hr=$("$npudr" v3render $t "$p.rust/$t.json" /dev/stdout 2>"$p.$t.rerr" | sha256sum | cut -c1-64)
                    else
                      $HEAVY "$lsq" render $t "$d" "$p.$t.lean.bin" $prefix 2>"$p.$t.lerr"
                      nb=$(stat -c %s "$p.$t.lean.bin" 2>/dev/null || echo 0)
                      hl=$(sha256sum < "$p.$t.lean.bin" | cut -c1-64)
                      hr=$("$npudr" v3render $t "$p.rust/$t.json" /dev/stdout 2>/dev/null | head -c "$nb" | sha256sum | cut -c1-64)
                      rm -f "$p.$t.lean.bin"
                    fi ;;
          *) hl=$($HEAVY "$lsq" render $t "$d" - 2>"$p.$t.lerr" | sha256sum | cut -c1-64)
             hr=$("$npudr" v3render $t "$p.rust/$t.json" /dev/stdout 2>"$p.$t.rerr" | sha256sum | cut -c1-64) ;;
        esac
        if [ -z "$hl" ] || [ "$hl" != "$hr" ]; then rok=0; bad "$case $t: Rust and Lean renders differ ($(head -c 120 "$p.$t.lerr" 2>/dev/null))"; fi
      done
      [ $rok = 1 ] && nren=$((nren + 1)) && [ $full = 1 ] && nfull=$((nfull + 1))
    fi
    # 5. buses (other participants: trie and receipt sides from the same claim + witness)
    for t in ups val walk; do "$npudr" v3trie "$d" $t > "$p.$t.json" 2>/dev/null || bad "$case: v3trie $t failed"; done
    "$npudr" v3rcptfam "$d/claim.bin" "$d/witness.bin" "$p.rf" --no-prefix > /dev/null 2>&1 || bad "$case: v3rcptfam failed"
    bok=1
    sbus "$p.rust" "$p" "$BUS_A" "$p.busA" || { bok=0; bad "$case: unbalanced: $(grep FAIL "$p.busA" | tr '\n' ' ' | cut -c1-200)"; }
    if [ "${SCHEDQV_RCPT:-1}" = 1 ]; then
      sbus "$p.rust" "$p" "$BUS_B" "$p.busB" || { bok=0; bad "$case: unbalanced: $(grep FAIL "$p.busB" | tr '\n' ' ' | cut -c1-200)"; }
    fi
    [ $bok = 1 ] && nbus=$((nbus + 1))
    [ $tok = 1 ] && [ $bok = 1 ] && pass "$case: honest sched/ChaCha/qv ($sz): 9 tables v3check, buses balanced"
    rm -rf "$p.prep"
  done
done
[ $ncase -gt 0 ] || bad "schedqv: no fixture dumped"
echo "   ($ncase cases: Rust == Lean entries $nrust, v3check $ntab, renders identical $nren ($nfull with full 2^22 dumps), buses $nbus)"
[ $nrust = $ncase ] && pass "Rust v3sched == np-lean-sched-v3 on all $ncase cases"
[ $ntab = $ncase ] && pass "v3check: tables 8-15, 22 on honest entries of all $ncase cases"
[ "${SCHEDQV_RENDER:-1}" = 1 ] && [ $nren = $ncase ] && pass "Rust == Lean native renders (9 tables) on all $ncase cases ($nfull full 2^22)"
[ $nbus = $ncase ] && pass "buses $BUS_A$([ "${SCHEDQV_RCPT:-1}" = 1 ] && echo ",$BUS_B") balanced on all $ncase cases"

echo "== schedqv: Lean scheduler sampler (ActualRun.run with requests) vs npudr v3sched --rerun"
nsam=0
for seed in ${SCHEDQV_SEEDS:-1 2 3}; do
  for cfg in "3 4 12" "2 8 40" "1 16 200"; do
    set -- $cfg; sd="$so/sample-$seed-$1-$2-$3"
    if ! $HEAVY "$lss" sample $seed $1 $2 $3 "$sd" > "$sd.log" 2>&1; then bad "Lean sampler seed=$seed $cfg failed"; continue; fi
    nr=$(python3 -c "import json;b=json.load(open('$sd/sched.json'));print('%d blocks, %d requests, %d rounds' % (len(b), sum(len(x['run']['conv']) for x in b), sum(len(x['run']['rounds']) for x in b)))")
    if "$npudr" v3sched --rerun "$sd/sched.json" > "$sd/rerun.json" 2>"$sd/rerun.err" && python3 -c "
import json,sys; a=json.load(open('$sd/sched.json')); b=json.load(open('$sd/rerun.json'))
sys.exit(0 if [(x['run'],x['gb']) for x in a]==[(x['run'],x['gb']) for x in b] else 1)"; then
      pass "sampler seed=$seed ($cfg: $nr): Rust ActualRun.run + distributeEv == Lean"; nsam=$((nsam + 1))
    else bad "sampler seed=$seed ($cfg): Rust rerun differs ($(head -c 120 "$sd/rerun.err"))"; fi
    # internal scheduler / ChaCha buses on the sampled blocks (no public segment on these buses)
    tape=$(ls "$so"/*.tape 2>/dev/null | head -1)
    if [ -n "$tape" ] && "$npudr" v3bus "$air" "$tape" 40,41,42,43,44,45,46,47,48,49,50,57,58,62 \
         codec="$sd/sched.json" scandist="$sd/sched.json" proc="$sd/sched.json" mem="$sd/sched.json" cmp="$sd/sched.json" \
         chacha="$sd/chacha.json" rng="$sd/rng.json" shuf="$sd/shuf.json" > "$sd.bus" 2>&1; then
      pass "sampler seed=$seed ($cfg): SCMP SOP SFIN SINC SPUSH SSIN SSOUT SSMEM SGEN SSHUF SCHACHA SDLX SDG SA0 balanced"
    else bad "sampler seed=$seed ($cfg): internal buses unbalanced: $(grep FAIL "$sd.bus" | tr '\n' ' ' | cut -c1-160)"; fi
  done
done
[ $nsam -gt 0 ] || bad "schedqv: no sampler case"

echo "== schedqv: negatives (mutated honest entries must unbalance a bus; wrong witnesses are rejected)"
# sneg <case prefix> <label> <python mutation of e (dict of tables), B = the block list> <buses>
sneg() {
  local p=$1 lbl=$2 py=$3 bs=$4 q="$1.neg"
  rm -rf "$q"; cp -r "$p.rust" "$q"
  python3 - "$q" "$py" <<'PY'
import json, os, sys
d, py = sys.argv[1:3]
T = ["codec", "scandist", "proc", "mem", "cmp", "chacha", "rng", "shuf", "qv"]
e = {t: json.load(open(os.path.join(d, t + ".json"))) for t in T}
B = e["codec"]
exec(py)
for t in ["codec", "scandist", "proc", "mem", "cmp"]: e[t] = B
for t in T: json.dump(e[t], open(os.path.join(d, t + ".json"), "w"))
PY
  if sbus "$q" "$p" "$bs" "$q.bus"; then bad "$lbl: buses $bs still balanced"
  else pass "$lbl: unbalanced ($(grep FAIL "$q.bus" | head -2 | tr '\n' ' ' | cut -c1-90))"; fi
  rm -rf "$q"
}
nn=0
# negative cases: fixtures with an implicit step and queue records (summary.json)
negcases=$(for f in "$so"/*.lean/summary.json; do
  python3 -c "import json,sys;s=json.load(open('$f'));sys.exit(0 if s['blocks']>1 and s['qv_records']>0 else 1)" \
    && c=$(basename "$(dirname "$f")" .lean) && [ -f "$so/$c.tape" ] && echo "$c"; done | head -"${SCHEDQV_NEG_CASES:-3}")
for case in $negcases; do
  p="$so/$case"
  sneg "$p" "$case: prior value id of block 0 +1" "B[0]['vid'] += 1" "$BUS_A"
  sneg "$p" "$case: grid grant of link 0 +1" "B[0]['gb'][0] += 1" "$BUS_A"
  sneg "$p" "$case: all-shards hash byte flipped" "B[0]['ash'][0] ^= 1" "$BUS_A"
  sneg "$p" "$case: forwarding demand +1" "f = B[0]['fwd']; f[0][1] += 1 if f else 0; B[0]['fwd'] = f or [[0, 1]]" "$BUS_A"
  sneg "$p" "$case: link-0 INIT allowance +1" "B[0]['run']['segs'][0]['v0'] += 1" "$BUS_A"
  sneg "$p" "$case: allowed flag of link 1 flipped" "B[0]['allowed'][1] = not B[0]['allowed'][1]" "$BUS_A"
  sneg "$p" "$case: block instance tau changed" "B[0]['run']['tau'] = 1" "$BUS_A"
  sneg "$p" "$case: qv record users +1" "e['qv']['records'][0]['users'] += 1" "$BUS_A,$BUS_B"
  sneg "$p" "$case: qv record payload byte changed" "r = e['qv']['records'][-1]; k = 'bytes' if r['rkind'] == 2 else ('index' if r['rkind'] == 0 else 'entries'); r[k][0] = (r[k][0] ^ 1) if k != 'entries' else {'shard': [x ^ 1 for x in r[k][0]['shard']], 'index': r[k][0]['index']}" "$BUS_A,$BUS_B"
  sneg "$p" "$case: qv buffered walk vid +1" "e['qv']['walks'][1]['vid'] += 1" "$BUS_A,$BUS_B"
  sneg "$p" "$case: last qv walk dropped" "e['qv']['walks'].pop()" "$BUS_A,$BUS_B"
  nn=$((nn + 1))
done
[ $nn -gt 0 ] || bad "schedqv: no negative case ran"
# sampler negatives: the ChaCha lane must match the process table's shuffles
sd=$(ls -d "$so"/sample-*-2-8-40 2>/dev/null | head -1); tape=$(ls "$so"/*.tape 2>/dev/null | head -1)
if [ -n "$sd" ] && [ -n "$tape" ]; then
  lneg() { # lneg <label> <file> <python edit of x> <buses>
    cp "$sd/$2" "$sd/$2.orig"
    python3 -c "import json; x=json.load(open('$sd/$2')); $3; json.dump(x, open('$sd/$2','w'))"
    if "$npudr" v3bus "$air" "$tape" "$4" codec="$sd/sched.json" scandist="$sd/sched.json" proc="$sd/sched.json" \
         mem="$sd/sched.json" cmp="$sd/sched.json" chacha="$sd/chacha.json" rng="$sd/rng.json" shuf="$sd/shuf.json" > "$sd.neg" 2>&1
    then bad "sampler: $1: buses $4 still balanced"
    else pass "sampler: $1: unbalanced ($(grep FAIL "$sd.neg" | head -2 | tr '\n' ' ' | cut -c1-90))"; fi
    mv "$sd/$2.orig" "$sd/$2"
  }
  lneg "an RNG call dropped" rng.json "x.pop()" 45,46,47,48,49,50
  lneg "a shuffle value changed" shuf.json "x[0]['vals'][0] += 1" 45,46,47,48,49,50
  lneg "a ChaCha block dropped" chacha.json "x.pop()" 45,46,47,48,49,50
  lneg "a round entry's increase +1" sched.json "r=[r for b in x for r in b['run']['rounds']][0]; r['entries'][0]['inc'] += 1" 40,41,42,43,44
fi
# wrong witnesses: v3sched (and the Lean dumper) reject them
c1=$(ls "$fx" | head -1); c2=$(ls "$fx" | sed -n 2p); wq="$so/wrongw"; mkdir -p "$wq"
cp "$fx/$c1/claim.bin" "$wq/claim.bin"; cp "$fx/$c2/witness.bin" "$wq/witness.bin"
if "$npudr" v3sched "$wq" "$wq/out" > "$wq.log" 2>&1; then bad "v3sched accepts $c1's claim with $c2's witness"
else pass "v3sched rejects a foreign witness ($(tail -c 80 "$wq.log" | tr '\n' ' '))"; fi
head -c 100 "$fx/$c1/witness.bin" > "$wq/witness.bin"
if "$npudr" v3sched "$wq" "$wq/out" > "$wq.log" 2>&1; then bad "v3sched accepts a truncated witness"
else pass "v3sched rejects a truncated witness ($(tail -c 60 "$wq.log" | tr '\n' ' '))"; fi
if $HEAVY "$lsq" "$wq" "$wq/lout" > "$wq.llog" 2>&1; then bad "np-lean-sched-v3 accepts a truncated witness"
else pass "np-lean-sched-v3 rejects a truncated witness"; fi
