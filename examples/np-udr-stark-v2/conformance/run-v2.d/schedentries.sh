#!/usr/bin/env bash
# Scheduler-side real-witness entries (tables 11-15, 8-10): `np-lean-sched-v3`
# produces `sched.json` + the ChaCha lane files from a real D0a fixture; the
# Lean render (`np-lean-render-v3-sched`) and the Rust render (`npudr v3render`)
# must agree byte for byte on the common row prefix, and `npudr v3check` must
# accept the rendered table.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"
src="$here/../source"
if [ -z "${HEAVY+x}" ]; then
  if [ -x /data/illia/nearproof-deps/bin/heavy ]; then HEAVY=/data/illia/nearproof-deps/bin/heavy; else HEAVY=; fi
fi
export PATH="$HOME/.elan/bin:$PATH"
fail=0
pass() { echo "PASS  $*"; }
bad()  { echo "FAIL  $*"; fail=1; }
(cd "$src" && $HEAVY cargo build --release -q) || { echo "cargo build failed"; exit 2; }
(cd "$here" && $HEAVY lake build -q np-lean-sched-v3 np-lean-render-v3-sched np-lean-export-v3) || { echo "lake build failed"; exit 2; }
RD=/data/illia/nearproof-wt/v3-prover/oracle/fixtures/v3/public-d0a/d0
EX="$here/.lake/build/bin/np-lean-sched-v3"; LS="$here/.lake/build/bin/np-lean-render-v3-sched"
RS="$src/target/release/npudr"; OUT="${SCHEDENTS_OUT:-/tmp/schedentries}"; rm -rf "$OUT"; mkdir -p "$OUT"
"$here/.lake/build/bin/np-lean-export-v3" > "$OUT/nearAirV3.json"
n=0
for D in $(ls -d "$RD"/* | head -8); do
  rm -rf "$OUT/case"; $HEAVY "$EX" "$D" "$OUT/case" >/dev/null 2>&1 || { bad "$(basename "$D"): np-lean-sched-v3 failed"; continue; }
  ok=1
  for t in codec scandist proc mem cmp; do
    $HEAVY "$LS" render "$t" "$OUT/case/sched.json" "$OUT/L.bin" 64 >/dev/null 2>&1
    "$RS" v3render "$t" "$OUT/case/sched.json" "$OUT/R.bin" >/dev/null 2>&1
    python3 - "$OUT/L.bin" "$OUT/R.bin" <<'PY' || ok=0
import sys
l=open(sys.argv[1],'rb').read(); r=open(sys.argv[2],'rb').read()
lw=int.from_bytes(l[4:8],'little'); n=8+64*lw*4
sys.exit(0 if l[:n]==r[:n] else 1)
PY
  done
  # v3check one table against the AIR
  if "$RS" v3check "$OUT/nearAirV3.json" cmp "$OUT/case/sched.json" >/dev/null 2>&1; then :; else bad "$(basename "$D"): v3check cmp"; ok=0; fi
  [ $ok -eq 1 ] && { pass "$(basename "$D"): sched tables byte-identical"; n=$((n+1)); }
done
[ $n -gt 0 ] || bad "no fixture produced scheduler entries"
echo "   ($n cases)"
if [ $fail -eq 0 ]; then echo "ALL PASS"; else echo "SOME FAILED"; fi
exit $fail
