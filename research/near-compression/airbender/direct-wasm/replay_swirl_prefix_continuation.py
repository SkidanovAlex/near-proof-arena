"""Replay the public-prefix/GKR/weighted-PCS diagnostic in separate processes.

Uses a key-directed prefix codec and the new PCS tail. Public metadata and
GKR remain separate fixture artifacts; no security certificate is claimed.
"""
import gzip,json,os,subprocess
from pathlib import Path
from prepare_swirl_prefix_continuation import main as prepare, OUT
from prove_swirl_prefix_dag import BASE,PREFIX
REPO=Path('/tmp/nearproof-openvm')
CODEC=BASE/'prefix-codec'


def run(name,env,log):
    result=subprocess.run(['cargo','test','--locked','--profile','fast','-p','openvm-recursion-circuit',
        'tests::'+name,'--','--exact','--nocapture'],cwd=REPO,env=env,capture_output=True,text=True)
    (CODEC/log).write_text(result.stdout+result.stderr)
    assert result.returncode==0,(name,result.returncode,log)


def main():
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
    assert commit=='e74f9b1ee868c42776faf821b8b9f2e8829a7f68'
    env=os.environ.copy()
    for key in ('NEARPROOF_GKR_BINDING','NEARPROOF_WEIGHTED_WHIR','NEARPROOF_NATIVE_CAPTURE','NEARPROOF_PREFIX_ONLY','NEARPROOF_EXPORT_PREFIX'):env.pop(key,None)
    env['RAYON_NUM_THREADS']='4'
    prefix_path=Path('/tmp/nearproof-retained-prefix.bin')
    prefix_path.write_bytes((BASE/'prefix-codec/prefix.bin').read_bytes())
    env['NEARPROOF_PREFIX_ONLY']=str(prefix_path)
    for src,dst in [('whir.proof.gz','nearproof-weighted-whir.proof'),('stacking.proof.gz','nearproof-weighted-stacking.proof')]:
        (Path('/tmp')/dst).write_bytes(gzip.decompress((OUT/src).read_bytes()))
    # Native verification decodes only retained prefix messages and validates shapes.
    run('nearproof_opening_free_prefix',env,'driver-native-prefix.log')
    assert json.loads(Path('/tmp/nearproof-prefix-trace-shapes.json').read_text())==json.loads((OUT/'trace-shapes.json').read_text())
    assert json.loads(Path('/tmp/nearproof-prefix-layouts.json').read_text())==json.loads((BASE/'committed-witness/layouts.json').read_text())
    assert json.loads(Path('/tmp/nearproof-opening-free-controls.json').read_text())==json.loads((PREFIX/'controls.json').read_text())
    assert Path('/tmp/nearproof-opening-free-prefix-log.txt').read_bytes()==gzip.decompress((PREFIX/'transcript-log.txt.gz').read_bytes())
    Path('/tmp/nearproof-reconstructed-witness').mkdir(exist_ok=True)
    prepare()  # Verifies GKR, derives weights, binds the exact statement/proof.
    for src,dst in [('whir.proof.gz','nearproof-weighted-whir.proof'),('stacking.proof.gz','nearproof-weighted-stacking.proof')]:
        (Path('/tmp')/dst).write_bytes(gzip.decompress((OUT/src).read_bytes()))
    env['NEARPROOF_GKR_BINDING']='/tmp/nearproof-prefix-gkr-binding.bin'
    run('nearproof_replay_weighted_whir',env,'driver-native-continuation.log')
    print('PASS: native prefix -> public GKR -> derived residual -> authenticated weighted WHIR; no original proof or source matrices read')


if __name__=='__main__':main()
