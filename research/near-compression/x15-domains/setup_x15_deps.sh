#!/usr/bin/env bash
# Pinned native deps (native/setup_native_deps.sh) + the x15 odd-domain research patch.
#   NEARPROOF_PQ_DEPS  target root (default /data/illia/nearproof-deps/pq-x15); never pq-native.
# Idempotent: an already-patched tree is verified (reverse-apply check), not re-patched.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-x15}
case "$DEPS" in */pq-native) echo "refusing to patch the shared pq-native tree" >&2; exit 1;; esac
B=$DEPS/stark-backend
P=$HERE/patches/stark-backend-x15.patch
if [ ! -f "$B/.x15-applied" ]; then
  NEARPROOF_PQ_DEPS=$DEPS "$HERE/../native/setup_native_deps.sh"
  git -C "$B" apply "$P"
  sha256sum "$P" | cut -d' ' -f1 > "$B/.x15-applied"
fi
[ "$(cat "$B/.x15-applied")" = "$(sha256sum "$P" | cut -d' ' -f1)" ] || { echo "x15 patch changed since apply" >&2; exit 1; }
git -C "$B" apply --reverse --check "$P" || { echo "stark-backend tree differs from pinned + x15 patch" >&2; exit 1; }
echo "x15 deps OK: $DEPS"
