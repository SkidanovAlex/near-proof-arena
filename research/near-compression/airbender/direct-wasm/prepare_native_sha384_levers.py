"""Prepare the native SHA-384/Ext12 crate with the proof-size-lever driver.

Same as prepare_native_sha384.py (same literal input handling, Cargo.toml and
lockfile) but installs native_sha384_levers_{driver,config}.rs. Build it against
a backend tree made by native/setup_levers_deps.sh (NEARPROOF_PQ_DEPS).
"""
from pathlib import Path
import shutil, argparse, sys
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).parent
sys.path.insert(0, str(ROOT / 'native'))
import native_paths  # noqa: E402
native_paths.require_deps()
TMP = native_paths.CRATE
(TMP / 'src').mkdir(parents=True, exist_ok=True)
ap = argparse.ArgumentParser()
ap.add_argument('--literal-source', type=Path, required=True)
ap.add_argument('--out', type=Path, required=True)
args = ap.parse_args()
OUT = args.out.resolve(); OUT.mkdir(exist_ok=True)
ret = args.literal_source.resolve()
for name in ['fixture.json', 'spec.json', 'public.bin'] + [p.name for p in sorted(ret.glob('rows-*.bin'))]:
    shutil.copyfile(ret / name, OUT / name)
if (ret / 'packing.json').exists():
    shutil.copyfile(ret / 'packing.json', OUT / 'packing.json')
s = (ret / 'native_literal.rs').read_text().split('// Appended to the generated literal AIR adapter.')[0]
s = s.replace('BabyBearPoseidon2Config', 'SC').replace('struct LiteralFixture;', 'pub(super) struct LiteralFixture;')
(TMP / 'src/literal.rs').write_text(s)
for name, dst in [('native_sha384_levers_driver.rs', 'main.rs'),
                  ('native_sha384_levers_config.rs', 'native_sha384_levers_config.rs'),
                  ('native_digest_dictionary.rs', 'native_digest_dictionary.rs')]:
    shutil.copyfile(HERE / name, TMP / 'src' / dst)
backend = native_paths.BACKEND / 'crates/stark-backend'
(TMP / 'Cargo.toml').write_text(f'''[package]
name="nearproof-native-sha384"
version="0.1.0"
edition="2024"
[dependencies]
openvm-stark-backend={{path="{backend}",default-features=false,features=["test-utils","parallel"]}}
p3-baby-bear="=0.4.3"
p3-field="=0.4.3"
p3-air="=0.4.3"
p3-matrix="=0.4.3"
sha2="=0.10.9"
[patch.crates-io]
p3-baby-bear={{path="{native_paths.EXT12}/p3-baby-bear"}}
p3-monty-31={{path="{native_paths.EXT12}/p3-monty-31"}}
''')
shutil.copyfile(native_paths.LOCKFILE, TMP / 'Cargo.lock')
print(TMP, OUT)
