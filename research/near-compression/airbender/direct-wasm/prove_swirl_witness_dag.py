"""GKR fixture bound to the new proof whose committed matrices are preserved."""
import shutil
import sys
from prove_swirl_native_dag import ROOT, fixture
from prove_swirl_weighted_dag import main, replay
from group_swirl_pcs_pairs import main as group

SOURCE=ROOT/'results/swirl-security-review/committed-witness'
OUT=ROOT/'results/swirl-security-review/witness-dag-gkr'


def build():
    return fixture(SOURCE/'point-capture.jsonl.gz', SOURCE/'openings.json.gz', OUT)


if __name__=='__main__':
    OUT.mkdir(exist_ok=True)
    shutil.copy(SOURCE/'openings.json.gz', OUT/'openings.json.gz')
    if sys.argv[1:]==['--verify-saved']:
        replay(build, OUT)
    else:
        assert not sys.argv[1:]
        main(build, OUT, 'Fresh native proof with preserved committed witness. Original proof/capture still required; not a replacement transcript.')
    group(OUT, OUT)
