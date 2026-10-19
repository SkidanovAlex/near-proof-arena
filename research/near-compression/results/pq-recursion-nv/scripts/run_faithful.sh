#!/usr/bin/env bash
# NV-faithful checks (FAITHFUL.md): DOF perturbation of every cell (4 fixtures), tamper tests,
# LogUp counts, SHA/transcript tests; 48-byte and 42-byte + coset-leaf modes; carry bounds.
#   NV_TREE   openvm-sha384 tree with the patch applied (setup_recursion_deps.sh)
#   NV_DOF_CAP rows per (AIR, role) to perturb (0 = every row; default 0)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
NV_TREE=${NV_TREE:-/data/illia/nearproof-deps/pq-nv-soundness/openvm-sha384}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-/data/illia/nearproof-deps/pq-nv-soundness-target}
export NV_DOF_CAP=${NV_DOF_CAP:-0}
python3 -I "$HERE/sha_carry_bounds.py" | tail -1
cd "$NV_TREE"
run() { HEAVY_MEM=16G taskset -c 0-31 /data/illia/nearproof-deps/bin/heavy \
  cargo test --release -p openvm-recursion-circuit --lib -- nv_ --skip nv_chain --skip nv_app_binding --test-threads 2; }
run
NEARPROOF_COSET_LEAF=1 NEARPROOF_DIGEST_BYTES=42 run
