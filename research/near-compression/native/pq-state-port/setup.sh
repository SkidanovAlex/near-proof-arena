#!/usr/bin/env bash
# Own copy of the unified SWIRL research backend used by lane/pq-wasm-base (stark-backend d667af5 +
# native base patch + stark-backend-unified overlay, plonky3-ext12), under NEARPROOF_PQ_DEPS
# (default /data/illia/nearproof-deps/pq-state-port).  Source: /data/illia/nearproof-deps/pq-wasm-base
# (copied, not linked).  The overlay diff of the tree used for the recorded runs has
# sha256 051a037b56a30161dee4d71eae9d56af776daa86a4390a99867bc3881b515214 (`git diff HEAD | sha256sum`).
set -euo pipefail
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-state-port}
SRC=${SRC:-/data/illia/nearproof-deps/pq-wasm-base}
mkdir -p "$D"
[ -d "$D/stark-backend-unified/.git" ] || cp -a "$SRC/stark-backend-unified" "$D/"
[ -f "$D/plonky3-ext12/p3-baby-bear/Cargo.toml" ] || cp -a "$SRC/plonky3-ext12" "$D/"
[ "$(git -C "$D/stark-backend-unified" log -1 --format=%s)" = "nearproof base patch (stark-backend-d667af5.patch)" ] \
  || { echo "base commit is not the native base patch" >&2; exit 1; }
h=$(git -C "$D/stark-backend-unified" diff HEAD | sha256sum | cut -d' ' -f1)
[ "$h" = 051a037b56a30161dee4d71eae9d56af776daa86a4390a99867bc3881b515214 ] || echo "warning: overlay diff $h differs from the recorded tree" >&2
echo "pq-state-port deps OK: $D"
