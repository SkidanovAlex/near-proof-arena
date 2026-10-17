"""Measure root-split terminal GKR on its own matched native proof.

Uses the capture-bound diagnostic statement. Opening-free native prefix export
and authenticated continuation for this new key remain separate integration.
"""
import sys
from prove_swirl_native_dag import ROOT,fixture
from prove_swirl_weighted_dag import main,replay
SOURCE=ROOT/'results/swirl-security-review/root-split-witness'
OUT=ROOT/'results/swirl-security-review/root-split-dag-gkr'


def build():
    return fixture(SOURCE/'point-capture.jsonl.gz',SOURCE/'openings.json.gz',OUT,SOURCE/'dag.jsonl.gz')


if __name__=='__main__':
    OUT.mkdir(exist_ok=True)
    if sys.argv[1:]==['--verify-saved']:replay(build,OUT)
    else:
        assert not sys.argv[1:]
        main(build,OUT,'Root-split matched witness fixture with capture-bound statement; diagnostic component measurement only, not compressed root verification.')
