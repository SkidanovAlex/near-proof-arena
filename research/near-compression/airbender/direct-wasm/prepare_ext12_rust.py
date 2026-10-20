"""Check the pinned Ext12 Plonky3 tree against its construction; prepare the arithmetic check crate.

The patched crates come from native/setup_native_deps.sh; this script never edits them."""
from pathlib import Path
import json,shutil,difflib
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/babybear-ext12-construction'
import sys;sys.path.insert(0,str(ROOT/'native'));import native_paths
native_paths.require_deps()
TMP=native_paths.DEPS/'ext12-check';TMP.mkdir(exist_ok=True)
c=json.loads((OUT/'construction.json').read_text())
patches=[]
for name in ['p3-baby-bear','p3-monty-31']:
    src=native_paths.EXT12/'.orig'/name;dst=native_paths.EXT12/name
    rel='src/baby_bear.rs' if name=='p3-baby-bear' else 'src/extension.rs'
    old=(src/rel).read_text();new=old
    if name=='p3-baby-bear':
        new+='\nimpl BinomialExtensionData<12> for BabyBearParameters {\n'
        new+=f' const W: BabyBear = BabyBear::new(31);\n const DTH_ROOT: BabyBear = BabyBear::new({c["dth_root"]});\n'
        new+=f' const EXT_GENERATOR: [BabyBear;12] = BabyBear::new_array({c["generator"]});\n'
        new+=' const EXT_TWO_ADICITY: usize = 29;\n type ArrayLike = [[BabyBear;12];2];\n'
        new+=f' const TWO_ADIC_EXTENSION_GENERATORS: Self::ArrayLike = BabyBear::new_2d_array({c["two_adic_roots"]});\n}}\n'
    else:
        new=new.replace('_w: Self)', 'w: Self)')
        new=new.replace('_ => panic!("Unsupported binomial extension degree: {}", WIDTH),', '''12 => {
                res.fill(Self::ZERO);
                for i in 0..WIDTH {
                    for j in 0..WIDTH {
                        let product = a[i] * b[j];
                        if i+j < WIDTH { res[i+j] += product; }
                        else { res[i+j-WIDTH] += product*w; }
                    }
                }
            },
            _ => panic!("Unsupported binomial extension degree: {}", WIDTH),''')
        assert new!=old
    assert (dst/rel).read_text()==new,f'{dst/rel} differs from construction'
    patches.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=f'a/{name}/{rel}',tofile=f'b/{name}/{rel}'))
(OUT/'plonky3-ext12.patch').write_text(''.join(patches))
(TMP/'Cargo.toml').write_text('''[package]
name="nearproof-ext12-check"
version="0.1.0"
edition="2024"
[dependencies]
p3-baby-bear="=0.4.3"
p3-field="=0.4.3"
serde_json="1"
[patch.crates-io]
p3-baby-bear={path="EXT12/p3-baby-bear"}
p3-monty-31={path="EXT12/p3-monty-31"}
'''.replace('EXT12',str(native_paths.EXT12)))
(TMP/'src').mkdir(exist_ok=True)
shutil.copyfile(Path(__file__).with_name('ext12_check.rs'),TMP/'src/main.rs')
print(TMP)
