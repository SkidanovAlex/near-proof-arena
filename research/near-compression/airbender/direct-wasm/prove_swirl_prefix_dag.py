"""GKR statement bound to the opening-free native prefix, not witness nodes.

This fixture still obtains witness inputs from saved openings. The new native
prefix API supplies verifier controls without reading those openings.
"""
import gzip,hashlib,json,sys
from prove_swirl_native_dag import ROOT, fixture
from prove_swirl_weighted_dag import main,replay
import pq384_terminal_gkr as g

BASE=ROOT/'results/swirl-security-review'
PREFIX=BASE/'opening-free-prefix'
SOURCE=BASE/'committed-witness'
OUT=BASE/'prefix-dag-gkr'


def build():
    controls=json.loads((PREFIX/'controls.json').read_text())
    original=json.loads(gzip.decompress((SOURCE/'point-capture.jsonl.gz').read_bytes()))
    expected={k:v for k,v in original.items() if k not in ('traces','evaluated_claim')}
    expected['traces']=[{k:v for k,v in trace.items() if k!='nodes'} for trace in original['traces']]
    assert controls==expected
    log=gzip.decompress((PREFIX/'transcript-log.txt.gz').read_bytes())
    statement_description=dict(profile='nearproof-opening-free-prefix-gkr-v1',
        prefix_log_sha384=hashlib.sha384(log).hexdigest(),controls=controls)
    statement=hashlib.sha384(json.dumps(statement_description,sort_keys=True,separators=(',',':')).encode()).digest()
    values=list(fixture(SOURCE/'point-capture.jsonl.gz',SOURCE/'openings.json.gz',OUT))
    values[-1]=statement
    (OUT/'statement.json').write_text(json.dumps(statement_description,indent=2)+'\n')
    return tuple(values)


if __name__=='__main__':
    OUT.mkdir(exist_ok=True)
    if sys.argv[1:]==['--verify-saved']:replay(build,OUT)
    else:
        assert not sys.argv[1:]
        main(build,OUT,'Verifier statement contains opening-free native prefix log hash and public controls; witness openings remain prover inputs. No combined PCS/transcript security theorem.')

    _,layout,_,_,_,claim,statement=build()
    proof=json.loads(gzip.decompress((OUT/'proof.json.gz').read_bytes()))
    old=json.loads(gzip.decompress((BASE/'witness-dag-gkr/proof.json.gz').read_bytes()))
    rejected=[]
    for label,st,p in [('changed_prefix_digest',bytes([statement[0]^1])+statement[1:],proof),
                       ('old_capture_bound_proof',statement,old)]:
        try:g.verify(layout,st,p,claim)
        except ValueError:rejected.append(label)
        else:raise AssertionError(label+' accepted')
    (OUT/'statement-binding.json').write_text(json.dumps({'rejected':rejected})+'\n')
    print('PASS: prefix statement binding',rejected)
