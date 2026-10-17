"""Root-split GKR bound to its opening-free public native prefix."""
import gzip,hashlib,json,sys
from prove_swirl_native_dag import ROOT,fixture
from prove_swirl_weighted_dag import main,replay,split_obligation
from verify_swirl_prefix_dag import public_context
import pq384_terminal_gkr as g
SOURCE=ROOT/'results/swirl-security-review/root-split-witness'
OUT=ROOT/'results/swirl-security-review/root-split-public-gkr'


def context():
    c=json.loads((SOURCE/'public-controls.json').read_text())
    log=gzip.decompress((SOURCE/'public-prefix-log.txt.gz').read_bytes())
    return public_context(c,log,SOURCE/'dag.jsonl.gz')


def build():
    data=list(fixture(SOURCE/'point-capture.jsonl.gz',SOURCE/'openings.json.gz',OUT,SOURCE/'dag.jsonl.gz'))
    layout,slots,known,claim,statement,description=context()
    assert layout==data[1] and slots==data[2] and known==data[4] and claim==data[5]
    data[-1]=statement
    (OUT/'statement.json').write_text(json.dumps(description,indent=2)+'\n')
    return tuple(data)


def public_replay():
    layout,slots,known,claim,statement,_=context()
    proof=json.loads(gzip.decompress((OUT/'proof.json.gz').read_bytes()))
    residual=split_obligation(g.verify(layout,statement,proof,claim),slots,known)
    expected=json.loads(gzip.decompress((OUT/'pcs-obligation.json.gz').read_bytes()))
    assert json.loads(json.dumps(residual))==expected
    report=dict(status='ROOT_PUBLIC_GKR_REPLAYED',known_slots=len(known),pcs_coordinates=len(residual['coordinates']),
                scope='Root prefix controls and fixed root DAG only; no source column openings read by this replay. Root PCS continuation remains pending.')
    (OUT/'public-replay.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':
    OUT.mkdir(exist_ok=True)
    if sys.argv[1:]==['--verify-public']:public_replay()
    elif sys.argv[1:]==['--verify-saved']:replay(build,OUT)
    else:
        assert not sys.argv[1:]
        main(build,OUT,'Root-split public prefix statement; matched root witness used only by prover. Root weighted PCS and PQ128 remain unimplemented.')
        public_replay()
