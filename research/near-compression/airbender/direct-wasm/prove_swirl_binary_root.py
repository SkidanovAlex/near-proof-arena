"""Generate a fresh GKR proof and native continuation inputs for v2 bindings."""
import gzip,json,shutil
from pathlib import Path
from prove_swirl_root_public_dag import SOURCE
from prove_swirl_native_dag import fixture
from prove_swirl_weighted_dag import main as prove
from verify_swirl_prefix_dag import public_context
from prepare_swirl_prefix_continuation import main as prepare
OUT=SOURCE.parent/'binary-root-gkr'


def context():
    c=json.loads((SOURCE/'public-controls.json').read_text())
    log=None
    return public_context(c,log,SOURCE/'dag.jsonl.gz',(SOURCE/'prefix.bin').read_bytes())


def build():
    data=list(fixture(SOURCE/'point-capture.jsonl.gz',SOURCE/'openings.json.gz',OUT,SOURCE/'dag.jsonl.gz'))
    layout,slots,known,claim,statement,_=context()
    assert layout==data[1] and slots==data[2] and known==data[4] and claim==data[5]
    data[-1]=statement;return tuple(data)


def main():
    prove(build,OUT,'Version2 binary prefix statement; native continuation pending.')
    proof=json.loads(gzip.decompress((OUT/'proof.json.gz').read_bytes()))
    report=prepare(proof,json.loads((SOURCE/'public-controls.json').read_text()),
        None,
        json.loads((SOURCE/'trace-shapes.json').read_text()),json.loads((SOURCE/'layouts.json').read_text()),
        write_outputs=False,dag_path=SOURCE/'dag.jsonl.gz',prefix_bytes=(SOURCE/'prefix.bin').read_bytes())
    for src,dst in [('/tmp/nearproof-reconstructed-witness/weighted-input.bin','weighted-input.bin'),('/tmp/nearproof-prefix-gkr-binding.bin','gkr-binding.bin')]:shutil.copy(src,OUT/dst)
    shutil.copy(OUT/'weighted-input.bin','/tmp/nearproof-root-split-witness/weighted-input.bin')
    (OUT/'preparation.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
