"""Prepare standalone actual-Wasm child using SHA-384 and degree12 candidate."""
from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).parent
TMP=Path('/tmp/nearproof-native-sha384');(TMP/'src').mkdir(parents=True,exist_ok=True)
OUT=ROOT/'results/native-literal-sha384-ext12-compact';OUT.mkdir(exist_ok=True)
ret=ROOT/'results/native-literal-field-screen'
for name in ['fixture.json','spec.json','rows-0.bin','rows-1.bin','public.bin']:shutil.copyfile(ret/name,OUT/name)
s=(ret/'native_literal.rs').read_text().split('// Appended to the generated literal AIR adapter.')[0]
s=s.replace('BabyBearPoseidon2Config','SC').replace('struct LiteralFixture;','pub(super) struct LiteralFixture;')
(TMP/'src/literal.rs').write_text(s)
for name,dst in [('native_sha384_driver.rs','main.rs'),('native_sha384_config.rs','native_sha384_config.rs')]:shutil.copyfile(HERE/name,TMP/'src'/dst)
backend='/home/illia/.cargo/git/checkouts/stark-backend-708f1155344bec0c/d667af5/crates/stark-backend'
(TMP/'Cargo.toml').write_text(f'''[package]
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
p3-baby-bear={{path="/tmp/nearproof-ext12-rust/p3-baby-bear"}}
p3-monty-31={{path="/tmp/nearproof-ext12-rust/p3-monty-31"}}
''')
print(TMP,OUT)
