#!/usr/bin/env bash
# Build the x15 prototype driver twice:
#   $DEPS/x15-proto       -> patched backend in $DEPS/stark-backend (feature x15)
#   $DEPS/x15-proto-base  -> unmodified pinned backend in $BASE_DEPS/stark-backend (byte-identity)
# Usage: NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-x15 setup_x15_crate.sh
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
NC=$(cd "$HERE/../native" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-x15}
BASE_DEPS=${NEARPROOF_PQ_BASE_DEPS:-/data/illia/nearproof-deps/pq-native}
CONFIG_RS=$(cd "$HERE/../airbender/direct-wasm" && pwd)/native_sha384_config.rs
for v in "x15-proto:$DEPS:x15" "x15-proto-base:$BASE_DEPS:"; do
  IFS=: read -r name root feat <<<"$v"
  d=$DEPS/$name; mkdir -p "$d"
  ln -sfn "$HERE/crate/src" "$d/src"
  cat > "$d/Cargo.toml" <<TOML
[package]
name="$name"
version="0.1.0"
edition="2024"
[features]
x15=[]
default=[${feat:+\"$feat\"}]
[dependencies]
openvm-stark-backend={path="$root/stark-backend/crates/stark-backend",default-features=false,features=["test-utils","parallel"]}
p3-baby-bear="=0.4.3"
p3-field="=0.4.3"
p3-air="=0.4.3"
p3-matrix="=0.4.3"
sha2="=0.10.9"
[patch.crates-io]
p3-baby-bear={path="$root/plonky3-ext12/p3-baby-bear"}
p3-monty-31={path="$root/plonky3-ext12/p3-monty-31"}
[profile.release]
debug=false
TOML
  [ -f "$d/Cargo.lock" ] || cp "$NC/crate/Cargo.lock" "$d/Cargo.lock"
  mkdir -p "$d/.cargo"; printf '[env]\nNEARPROOF_SHA384_CONFIG_RS="%s"\n' "$CONFIG_RS" > "$d/.cargo/config.toml"
done
echo "x15 crates prepared under $DEPS (x15-proto, x15-proto-base)"
