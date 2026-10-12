# run-v2.d/sched.sh — nearAirV3 tables 0, 1 (SHA), 8–10 (ChaCha lane), 11–15
# (scheduler): Rust (`npudr v3render`) vs the executable Lean renders of the
# completeness proof (`np-lean-render-v3-sched`, conformance/RenderV3Sched.lean),
# `npudr v3check` against the exported nearAirV3, and broken entries that must
# violate a constraint.  Sourced by run-v2.sh / run-v2-section.sh with
# `here src out npudr HEAVY pass bad` in scope; outputs under $out/sched/.
#
# The scheduler tables (11–15) are rendered at the shared clock 2^22 rows
# (`SchedHeight`), so their dumps are 0.3–2 GB: by default they are compared as
# sha256 of the full dump for every case (SCHED_FULL=0: only the first
# SCHED_PREFIX_ROWS rows, which cover every non-padding row of the samples).
#
#   SCHED_SEEDS    seeds of the Rust samplers / Lean scheduler sampler (default "1 2 3")
#   SCHED_FULL     1 = full-dump sha256 for the 2^22 tables (default 1)

ls_=$here/.lake/build/bin/np-lean-render-v3-sched
sd="$out/sched"; mkdir -p "$sd"
air="$out/nearAirV3.json"
seeds=${SCHED_SEEDS:-1 2 3}
full=${SCHED_FULL:-1}
prefix=${SCHED_PREFIX_ROWS:-4096}

# same <table> <entries.json> <label>: Rust dump == Lean dump (whole file, or sha256
# of the stream for the 2^22 tables), then v3check.
same() {
  local t=$1 j=$2 x=$3 f="$sd/$(basename "$2" .json).$1"
  case $t in
    codec|scandist|proc|mem|cmp)
      if [ "$full" = 1 ]; then
        local hr hl
        hr=$("$npudr" v3render $t "$j" /dev/stdout | sha256sum | cut -c1-64)
        hl=$($HEAVY "$ls_" render $t "$j" - 2>"$f.err" | sha256sum | cut -c1-64)
        if [ -n "$hr" ] && [ "$hr" = "$hl" ]; then pass "$t $x: full 2^22 dump identical (sha256 ${hr:0:16})"
        else bad "$t $x: dump differs (rust ${hr:0:16} lean ${hl:0:16})"; cat "$f.err"; fi
      else
        local w nb
        $HEAVY "$ls_" render $t "$j" "$f.lean.bin" $prefix 2>"$f.err" || { bad "$t $x: Lean render failed"; cat "$f.err"; return; }
        nb=$(stat -c %s "$f.lean.bin")
        "$npudr" v3render $t "$j" /dev/stdout | head -c $nb > "$f.rust.bin"
        if cmp -s "$f.lean.bin" "$f.rust.bin"; then pass "$t $x: first $prefix rows identical"
        else bad "$t $x: first $prefix rows differ"; fi
        rm -f "$f.lean.bin" "$f.rust.bin"
      fi ;;
    *)
      $HEAVY "$ls_" render $t "$j" "$f.lean.bin" 2>"$f.err" || { bad "$t $x: Lean render failed"; cat "$f.err"; return; }
      "$npudr" v3render $t "$j" "$f.rust.bin" || { bad "$t $x: npudr v3render failed"; return; }
      if cmp -s "$f.lean.bin" "$f.rust.bin"; then pass "$t $x: trace identical ($(stat -c %s "$f.rust.bin") B)"
      else bad "$t $x: trace differs"; fi
      rm -f "$f.lean.bin" "$f.rust.bin" ;;
  esac
  if "$npudr" v3check "$air" $t "$j" >"$f.check" 2>&1; then pass "$t $x: $(cut -c5- "$f.check")"
  else bad "$t $x: constraints fail"; head -3 "$f.check"; fi
}

# 1. Rust samplers (SHA messages, ChaCha requests/calls/instances, request-free
#    scheduler blocks), sizes incl. 0 (the scheduler tables: no instance).
for t in sha_t chacha rng shuf; do
  for seed in $seeds; do for n in 1 5 37; do
    j="$sd/rs-$t-$seed-$n.json"; "$npudr" v3sample $t $seed $n > "$j"; same $t "$j" "rust sampler seed=$seed n=$n"
  done; done
  j="$sd/rs-$t-empty.json"; echo '[]' > "$j"; same $t "$j" "empty"
done
for seed in $seeds; do for n in 0 1 3; do
  j="$sd/rs-sched-$seed-$n.json"; "$npudr" v3sample codec $seed $n > "$j"
  for t in codec scandist proc mem cmp; do same $t "$j" "rust request-free blocks seed=$seed n=$n"; done
done; done

# 2. Lean scheduler sampler: native runs (`ActualRun.run`) with requests and rounds,
#    their ChaCha-lane entries (`laneReqs`/`laneCalls`/`laneInsts`), several instances.
for seed in $seeds; do
  for cfg in "1 2 6" "3 4 12"; do
    set -- $cfg; d="$sd/lean-$seed-$1-$2-$3"
    if ! $HEAVY "$ls_" sample $seed $1 $2 $3 "$d" >"$d.log" 2>&1; then bad "Lean sampler seed=$seed $cfg failed"; cat "$d.log"; continue; fi
    nr=$(python3 -c "import json;b=json.load(open('$d/sched.json'));print(len(b), sum(len(x['run']['rounds']) for x in b), sum(len(x['run']['conv']) for x in b))")
    pass "Lean sampler seed=$seed blocks/shards/reqs=($cfg): blocks, rounds, requests = $nr"
    for t in codec scandist proc mem cmp; do same $t "$d/sched.json" "native blocks seed=$seed ($cfg)"; done
    for t in chacha rng shuf; do
      cp "$d/$t.json" "$d/lane-$t.json"; same $t "$d/lane-$t.json" "native lane seed=$seed ($cfg)"
      # the Rust lane derivation (`chacha::lane`) from the same blocks renders the same table
      if cmp -s <("$npudr" v3render $t "$d/sched.json" /dev/stdout) <("$npudr" v3render $t "$d/lane-$t.json" /dev/stdout); then
        pass "$t seed=$seed ($cfg): Rust lane entries from runs == Lean laneReqs/laneCalls/laneInsts"
      else bad "$t seed=$seed ($cfg): Rust lane entries from runs differ"; fi
    done
  done
done

# 3. Broken entries: the rendered trace must violate a constraint.
broken() { # broken <table> <src.json> <label> <python edit of `es`>
  local t=$1 x=$3 f="$sd/broken-$1-$(echo "$3" | tr -c 'a-z0-9' _)"
  python3 -c "import json,sys; es=json.load(open('$2')); $4; print(json.dumps(es))" > "$f.json"
  if "$npudr" v3check "$air" $t "$f.json" >"$f.check" 2>&1; then bad "$t $x: constraints still hold"
  else pass "$t $x: constraint violated ($(head -1 "$f.check"))"; fi
}
L1="$sd/lean-1-3-4-12/sched.json"
R3="$sd/rs-sched-1-3.json"
broken proc "$R3" "instance step of 2 at a boundary" "es[2]['run']['tau'] += 1"
broken proc "$R3" "next instance with the same tau (no key-block step)" "es[1]['run']['tau'] = es[0]['run']['tau']"
broken proc "$L1" "round length Lr off by one" "r=[b for b in es if b['run']['rounds']][0]['run']['rounds'][0]; r['Lr'] += 1"
broken mem "$R3" "INIT vin != allowed flag" "s=es[0]['run']['segs'][0]; s['vin0'] = 1 - int(s['al'])"
broken cmp "$R3" "comparison with the wrong bit" "es[0]['run']['cmps'] = [[5, 3, 0]]"
broken codec "$R3" "prior hash byte 300" "b=es[0]; b['present']=True; b['a0']=[0]*(b['run']['n']**2); b['prev_hash']=[300]+[0]*31"
broken scandist "$L1" "request bitmap byte 300" "r=[b for b in es if b['run']['conv']][0]['run']['conv'][0]; r['bm'][0] = 300"
broken chacha "$sd/rs-chacha-1-5.json" "block counter 2^32" "es[0]['ctr'] = 2**32"
broken shuf "$sd/rs-shuf-1-5.json" "instance of length 20000 > 2^14 (stamp distance bits)" "es[1]['vals'] = list(range(20000))"
# A9: more than W0 = 770,000 drawn words (500k calls with n = 1, ~1M draws) must
# violate the last-row range check `Σ 2^e·Wb e = W0 − w` (rngV3 at 2^22 rows).
f="$sd/broken-rng-w0"
python3 -c "import json; print(json.dumps([{'key':[1,2,3,4,5,6,7,8],'kstart':i,'n':1} for i in range(500000)]))" > "$f.json"
if $HEAVY "$npudr" v3check "$air" rng "$f.json" >"$f.check" 2>&1; then bad "rng: > W0 drawn words: constraints still hold"
else pass "rng: > W0 drawn words: constraint violated ($(head -1 "$f.check"))"; fi
rm -f "$f.json"
