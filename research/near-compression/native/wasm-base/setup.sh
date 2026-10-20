#!/usr/bin/env bash
# Dependencies of the wasm-base crate: the pinned unified SWIRL research backend
# (stark-backend d667af5 + native base patch + stark-backend-unified.patch) and plonky3-ext12,
# under NEARPROOF_PQ_DEPS (default /data/illia/nearproof-deps/pq-wasm-base).
#   fresh tree:    ../setup_native_deps.sh, then ../recursion/setup_unified_deps.sh (pinned sources)
#   existing tree: verified against the patches (refuses on any difference)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-wasm-base}
U=$NEARPROOF_PQ_DEPS/stark-backend-unified
if [ ! -d "$U/.git" ]; then
  "$HERE/../setup_native_deps.sh"
  "$HERE/../recursion/setup_unified_deps.sh"
fi
diff <(git -C "$U" diff HEAD -- crates | grep -v '^index ') \
     <(grep -v '^index ' "$HERE/../recursion/patches/stark-backend-unified.patch") >/dev/null \
  || { echo "stark-backend-unified differs from patch" >&2; exit 1; }
[ "$(git -C "$U" log -1 --format=%s)" = "nearproof base patch (stark-backend-d667af5.patch)" ] \
  || { echo "stark-backend-unified: base commit is not the native base patch" >&2; exit 1; }
P=$NEARPROOF_PQ_DEPS/plonky3-ext12
[ -f "$P/p3-baby-bear/Cargo.toml" ] && [ -f "$P/p3-monty-31/Cargo.toml" ] || { echo "plonky3-ext12 missing" >&2; exit 1; }
echo "wasm-base deps OK: $NEARPROOF_PQ_DEPS"
echo "config.rs is a verbatim copy of openvm-sha384 crates/recursion/src/sha384/config.rs lines 1-669"
echo "(openvm-recursion-sha384.patch tree); compare with: diff <(sed -n 1,669p <that file>) src/config.rs"
