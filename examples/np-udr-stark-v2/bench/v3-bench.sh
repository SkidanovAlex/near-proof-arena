#!/usr/bin/env bash
# Per-workload benchmark of the np-udr-stark-v2 prover against the D0a
# challenge caps (prove <= 600 s, RAM <= 16 GiB, proof <= 8 MiB, verify <= 10 s).
#
#   bench/v3-bench.sh <cases-dir>...
#
# Each <cases-dir> holds case directories with request.bin, witness.bin and
# expected_claim.bin (oracle fixtures, e.g. oracle/fixtures/v3/public-d0a/d0).
#
# STATUS: the v3 proof path (nearAirV3 trace generation + the STARK prove over
# the 25-table AIR) is not implemented in Rust yet (README "Status"), so this
# script currently exercises only the inherited v1 `out/prove` surface and is a
# placeholder for the real D0a benchmark. Do not trust any numbers it prints
# until `npudr prove-v3` exists. It is kept so the package layout mirrors
# examples/np-udr-stark/bench/.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"
HEAVY=${HEAVY:-/data/illia/nearproof-deps/bin/heavy}
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
prove="$here/source/target/release/prove"
lv="$here/conformance/.lake/build/bin/np-lean-verify-v2"
if [ ! -x "$prove" ]; then
  echo "bench/v3-bench.sh: no prover at $prove; see README 'Status'" >&2
  exit 2
fi
echo "WARNING: v3 prover not implemented; results are not the D0a benchmark" >&2
printf "case\tn\tprove_s\tmaxrss_MB\tproof_B\tclaim\tlean_verify\tlean_ms\n"
work=$(mktemp -d)
pubdir="$work/public"; mkdir -p "$pubdir"
cp "${PUBLIC_BIN:-$here/../../oracle/fixtures/v3/arena-public/params.bin}" "$pubdir/public.bin"
for root in "$@"; do
  for d in "$root"/*/; do
    c=$(basename "$d")
    [ -f "$d/request.bin" ] || continue
    rm -f "$work/claim.bin" "$work/proof.bin"
    $HEAVY /usr/bin/time -v -o "$work/time" "$prove" --public "$pubdir" --request "$d/request.bin" \
      --witness "$d/witness.bin" --claim-out "$work/claim.bin" --proof-out "$work/proof.bin" 2>"$work/err" >/dev/null
    rc=$?
    secs=$(grep "Elapsed (wall" "$work/time" | awk '{print $NF}' | awk -F: '{ if (NF==2) print $1*60+$2; else print $1*3600+$2*60+$3 }')
    rss=$(grep "Maximum resident" "$work/time" | awk '{printf "%.0f", $NF/1024}')
    if [ $rc -ne 0 ]; then
      printf "%s\t-\t%s\t%s\tFAIL\t-\t-\t-\n" "$c" "$secs" "$rss"; continue
    fi
    n=$(stat -c %s "$work/proof.bin")
    cl=$(cmp -s "$work/claim.bin" "$d/expected_claim.bin" && echo ok || echo DIFF)
    lvr=-; lms=-
    if [ -x "$lv" ]; then
      lvr=$(HEAVY_MEM=4G $HEAVY "$lv" 2 "$here/source/near-air.json" "$pubdir/public.bin" "$work/claim.bin" "$work/proof.bin" 2>"$work/lerr")
      lms=$(grep -o 'wall [0-9]* ms' "$work/lerr" | awk '{print $2}')
    fi
    printf "%s\t-\t%s\t%s\t%s\t%s\t%s\t%s\n" "$c" "$secs" "$rss" "$n" "$cl" "$lvr" "$lms"
  done
done
rm -rf "$work"
