#!/usr/bin/env bash
# lane/pq-cpu-prover: the stream lane's real-settings NV chain (run_stream_chain.sh) with the fast CPU
# prover (setup_cpu_fast_deps.sh; test binary built with RUSTFLAGS="-C target-cpu=native").
# Original description (lane/pq-stream-commit): the real-settings NV chain, all streamed, in one process. Since
# lane/pq-recursion-sha384 717eb518e nv_chain runs phase A (natural heights, finds the fixed
# heights / app table), then phase B L1..L{NV_LEVELS} with binding on at every NV child, then the
# FINAL = the fixed-point program under the final domain (same shape as the penultimate), checked
# by V_d with the pinned program. FINAL_* is no longer used (MODE=bound, default); MODE=unbound
# keeps the pre-717eb518e invocation (268 bits = 236 query bits + z = 32 wide PoW, 42-B digests, coset
# leaves, x15, every lever; m = 64 + certificate-gated O-2 via NEARPROOF_DKT_CERTS).
#   run_cpu_chain.sh <tag>
# env: penultimate PB PNS PK PK1 PLF (default 7 18 4 2 6), final FB FNS FK FK1 FLF (7 18 4 1 7),
#      NV_LOG_ROWS (18), NV_PROG_LOG (18), BIN, CERTS, OUT, HEAVY_MEM (90G), NV_RESUME_PROOF (opt.)
set -uo pipefail
TAG=$1
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-cpu}
BIN=${BIN:-$DEPS/bin/nv-cf}
CERTS=${CERTS:-/data/illia/nearproof-wt/pq-dkt-verify/research/near-compression/final-soundness/calc/dkt_certs_o2.json}
EXCL=${EXCL:-/data/illia/nearproof-wt/pq-dkt-verify/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys}
OUT=${OUT:-$DEPS/ckpt/$TAG}
mkdir -p "$OUT"
LEV="X15=15 KEEP_DOMAIN=1 MULTIPROOF=1 GRUEN_GKR=1 GKR_DERIVE=1 GRUEN_ZC=1 NEXT_MASK=1 WHIR_Y=1 TIGHT=1 WIDE_POW=1 QUERY_POW=32 BITS=268 LIST_M=64 L_SKIP=2"
P=""; F=""
for x in $LEV; do P="$P PARENT_$x"; F="$F FINAL_$x"; done
if [ "${MODE:-bound}" = unbound ]; then
  FIN="$F FINAL_LOG_BLOWUP=${FB:-7} FINAL_N_STACK=${FNS:-18} FINAL_K=${FK:-4} FINAL_K1=${FK1:-1} FINAL_LOG_FINAL=${FLF:-7}"; NV_LEVELS_=0
else
  FIN=""; NV_LEVELS_=${NV_LEVELS:-3}
fi
RES=""; [ -n "${NV_RESUME_PROOF:-}" ] && RES="NV_RESUME_PROOF=$NV_RESUME_PROOF"
cd "$DEPS/openvm-sha384/crates/recursion"
{ date -u; free -g | head -2; sha256sum "$CERTS" "$EXCL"; } > "$OUT/run.log"
env HEAVY_MEM=${HEAVY_MEM:-90G} taskset -c 0-31 /data/illia/nearproof-deps/bin/heavy \
  env RAYON_NUM_THREADS=32 NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1 NEARPROOF_MEMPROF=1 \
  NEARPROOF_STREAM_COMMIT=1 NEARPROOF_STREAM_DROP=${NEARPROOF_STREAM_DROP:-4} NEARPROOF_DKT_CERTS="$CERTS" NEARPROOF_DKT_EXCLUDE="$EXCL" \
  NV_LEVELS=${NV_LEVELS_:-0} NV_PHASE_A=${NV_PHASE_A:-4} ${NV_FIXED_OVERRIDE:+NV_FIXED_OVERRIDE=$NV_FIXED_OVERRIDE} NV_LOG_ROWS=${NV_LOG_ROWS:-18} NV_PROG_LOG=${NV_PROG_LOG:-18} NV_SAVE_DIR="$OUT" $RES \
  $P PARENT_LOG_BLOWUP=${PB:-7} PARENT_N_STACK=${PNS:-18} PARENT_K=${PK:-4} PARENT_K1=${PK1:-2} PARENT_LOG_FINAL=${PLF:-6} \
  $FIN \
  /usr/bin/time -v "$BIN" nv::tests::nv_chain --ignored --exact --nocapture --test-threads 1 >> "$OUT/run.log" 2>&1
echo "EXIT $?" >> "$OUT/run.log"
