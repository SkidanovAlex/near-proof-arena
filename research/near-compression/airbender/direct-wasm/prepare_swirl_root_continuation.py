"""Derive root-specific weights/binding from its verified public GKR."""
import gzip,json,shutil
from pathlib import Path
from prepare_swirl_prefix_continuation import main as prepare
from prove_swirl_root_public_dag import SOURCE,OUT as GKR
OUT=SOURCE.parent/'root-split-continuation'


def main():
    OUT.mkdir(exist_ok=True)
    report=prepare(json.loads(gzip.decompress((GKR/'proof.json.gz').read_bytes())),
        json.loads((SOURCE/'public-controls.json').read_text()),gzip.decompress((SOURCE/'public-prefix-log.txt.gz').read_bytes()),
        json.loads((SOURCE/'trace-shapes.json').read_text()),json.loads((SOURCE/'layouts.json').read_text()),
        write_outputs=False,dag_path=SOURCE/'dag.jsonl.gz')
    for src,dst in [('/tmp/nearproof-reconstructed-witness/weighted-input.bin','weighted-input.bin'),('/tmp/nearproof-prefix-gkr-binding.bin','gkr-binding.bin')]:shutil.copy(src,OUT/dst)
    shutil.copy(OUT/'weighted-input.bin','/tmp/nearproof-root-split-witness/weighted-input.bin')
    (OUT/'preparation.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':main()
