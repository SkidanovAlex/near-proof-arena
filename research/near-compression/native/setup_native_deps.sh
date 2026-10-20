#!/usr/bin/env bash
# Rebuild the patched native dependencies of the SHA-384/Ext12 Wasm prover
# from pinned upstream sources plus the patches in ./patches.
#
# Replaces the earlier unpinned setup (patched shared ~/.cargo/git checkout
# and /tmp/nearproof-ext12-rust).  Idempotent: an existing tree is verified,
# never re-patched; a tree that fails verification is an error, not rebuilt.
#
#   NEARPROOF_PQ_DEPS  target root (default /data/illia/nearproof-deps/pq-native)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-native}

BACKEND_URL=https://github.com/openvm-org/stark-backend
BACKEND_REV=d667af5929d0ea9e5194adf639d6bddeb8c10f9a
declare -A CRATE_SHA256=(
  [p3-baby-bear]=3a1a49f4d9c8b8cbdab61e25d9de1b78b3c8347dd2fb88b11d990b3efa8cdd3a
  [p3-monty-31]=c9fe0be661891af1f703ceaf57334fcbd540804988984dc2b500dd99740e7c81
)
P3_VERSION=0.4.3

mkdir -p "$DEPS"

# stark-backend at the pinned revision, with research patches applied.
B=$DEPS/stark-backend
if [ ! -d "$B/.git" ]; then
  tmp=$(mktemp -d "$DEPS/.stark-backend.XXXX")
  git -C "$tmp" init -q
  git -C "$tmp" fetch -q --depth 1 "$BACKEND_URL" "$BACKEND_REV"
  git -C "$tmp" checkout -q --detach FETCH_HEAD
  git -C "$tmp" apply "$HERE/patches/stark-backend-d667af5.patch"
  mv "$tmp" "$B"
fi
[ "$(git -C "$B" rev-parse HEAD)" = "$BACKEND_REV" ] || { echo "stark-backend: wrong revision" >&2; exit 1; }
diff <(git -C "$B" diff | grep -v '^index ') <(grep -v '^index ' "$HERE/patches/stark-backend-d667af5.patch") >/dev/null \
  || { echo "stark-backend: working tree differs from pinned patch" >&2; exit 1; }

# Plonky3 0.4.3 crates from crates.io (checksummed), with the Ext12 patch.
P=$DEPS/plonky3-ext12
if [ ! -d "$P" ]; then
  tmp=$(mktemp -d "$DEPS/.plonky3.XXXX")
  for c in "${!CRATE_SHA256[@]}"; do
    curl -sSfL -o "$tmp/$c.crate" "https://static.crates.io/crates/$c/$c-$P3_VERSION.crate"
    echo "${CRATE_SHA256[$c]}  $tmp/$c.crate" | sha256sum -c --quiet -
    tar -xzf "$tmp/$c.crate" -C "$tmp"
    mv "$tmp/$c-$P3_VERSION" "$tmp/$c"
    rm "$tmp/$c.crate"
  done
  # Keep pristine copies for verification.
  mkdir "$tmp/.orig"
  cp -a "$tmp/p3-baby-bear" "$tmp/p3-monty-31" "$tmp/.orig/"
  (cd "$tmp" && patch -s -p1 < "$HERE/patches/plonky3-ext12.patch")
  mv "$tmp" "$P"
fi
diff <(cd "$P/.orig" && for c in p3-baby-bear p3-monty-31; do diff -ru "$c" "../$c" || true; done | grep -E '^[-+][^-+]') \
     <(grep -E '^[-+][^-+]' "$HERE/patches/plonky3-ext12.patch") >/dev/null \
  || { echo "plonky3-ext12: tree differs from pinned patch" >&2; exit 1; }

echo "native deps OK: $DEPS"
