#!/usr/bin/env bash
# Run one or more `run-v2.d/<name>.sh` sections of run-v2.sh on their own, with the
# same environment (no rebuild of the base targets, no toy proofs):
#
#   ./run-v2-section.sh <name> [<name> ...]
#
# Expects a built `npudr` (`$CARGO_TARGET_DIR` or ../source/target) and the Lean
# exes; `nearAirV3.json` is re-exported into `$out` if missing.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
src="$here/../source"
out="${OUT_V2:-$here/out-v2}"
if [ -z "${HEAVY+x}" ]; then
  if [ -x /data/illia/nearproof-deps/bin/heavy ]; then HEAVY=/data/illia/nearproof-deps/bin/heavy; else HEAVY=; fi
fi
export PATH="$HOME/.elan/bin:$PATH"
fail=0
pass() { echo "PASS  $*"; }
bad()  { echo "FAIL  $*"; fail=1; }
npudr="${CARGO_TARGET_DIR:-$src/target}/release/npudr"
lv="$here/.lake/build/bin/np-lean-verify-v2"
le="$here/.lake/build/bin/np-lean-export-v3"
lr="$here/.lake/build/bin/np-lean-render-v3"
le3="$here/.lake/build/bin/np-lean-entries-v3"
lp="$here/.lake/build/bin/np-lean-prep-v3"
fx="${FX:-$here/../../../oracle/fixtures/v3/public-d0a/d0}"
mkdir -p "$out"
[ -s "$out/nearAirV3.json" ] || "$le" > "$out/nearAirV3.json"
for n in "$@"; do
  echo "== section $n"
  # shellcheck disable=SC1090
  source "$here/run-v2.d/$n.sh"
done
echo
if [ $fail -eq 0 ]; then echo "ALL PASS"; else echo "SOME FAILED"; fi
exit $fail
