"""Pinned locations of the native SHA-384/Ext12 prover and its dependencies.

Populate them with native/setup_native_deps.sh; override the root with
NEARPROOF_PQ_DEPS.  The prepared crate (CRATE) is a generated work directory:
preparing a workload overwrites CRATE/src/literal.rs, so never prepare two
workloads against the same root concurrently.
"""
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEPS = Path(os.environ.get('NEARPROOF_PQ_DEPS', '/data/illia/nearproof-deps/pq-native'))
BACKEND = DEPS / 'stark-backend'
EXT12 = DEPS / 'plonky3-ext12'
CRATE = DEPS / 'native-sha384'
VECTORS_LOG = DEPS / 'native-sha384-vectors.log'
LOCKFILE = HERE / 'crate' / 'Cargo.lock'


def require_deps():
    for p in (BACKEND / '.git', EXT12 / 'p3-baby-bear', EXT12 / 'p3-monty-31'):
        if not p.exists():
            raise SystemExit(f'missing {p}: run {HERE / "setup_native_deps.sh"}')
