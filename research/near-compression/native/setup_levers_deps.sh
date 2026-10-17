#!/usr/bin/env bash
# Rebuild the native dependencies with the proof-size levers (lane/pq-whir-levers):
# the pinned tree of setup_native_deps.sh, plus patches/stark-backend-levers.patch layered
# on top of the stark-backend research patch.
#
# Layout of $DEPS/stark-backend: HEAD^ = pinned upstream revision, HEAD = local commit of
# patches/stark-backend-d667af5.patch, working tree = HEAD + patches/stark-backend-levers.patch.
# Idempotent: an existing tree is verified, never re-patched.
#
#   NEARPROOF_PQ_DEPS  target root (default /data/illia/nearproof-deps/pq-levers)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-levers}
DEPS=$NEARPROOF_PQ_DEPS
BACKEND_REV=d667af5929d0ea9e5194adf639d6bddeb8c10f9a
B=$DEPS/stark-backend
G=(git -C "$B" -c user.name=nearproof -c user.email=nearproof@localhost)
if [ ! -d "$B/.git" ]; then
  "$HERE/setup_native_deps.sh"          # pinned upstream + base patch, plonky3 Ext12
fi
if [ "$(git -C "$B" rev-parse HEAD)" = "$BACKEND_REV" ]; then
  # Fresh pinned tree: record the base patch as a local commit, then apply the levers.
  "${G[@]}" commit -q -a -m "nearproof base patch (stark-backend-d667af5.patch)"
  git -C "$B" apply "$HERE/patches/stark-backend-levers.patch"
fi
[ "$(git -C "$B" rev-parse HEAD^)" = "$BACKEND_REV" ] || { echo "stark-backend: wrong base revision" >&2; exit 1; }
diff <(git -C "$B" diff HEAD^ HEAD | grep -v '^index ') <(grep -v '^index ' "$HERE/patches/stark-backend-d667af5.patch") >/dev/null \
  || { echo "stark-backend: base commit differs from pinned patch" >&2; exit 1; }
diff <(git -C "$B" diff HEAD | grep -v '^index ') <(grep -v '^index ' "$HERE/patches/stark-backend-levers.patch") >/dev/null \
  || { echo "stark-backend: working tree differs from levers patch" >&2; exit 1; }
P=$DEPS/plonky3-ext12
diff <(cd "$P/.orig" && for c in p3-baby-bear p3-monty-31; do diff -ru "$c" "../$c" || true; done | grep -E '^[-+][^-+]') \
     <(grep -E '^[-+][^-+]' "$HERE/patches/plonky3-ext12.patch") >/dev/null \
  || { echo "plonky3-ext12: tree differs from pinned patch" >&2; exit 1; }
echo "native lever deps OK: $DEPS"
