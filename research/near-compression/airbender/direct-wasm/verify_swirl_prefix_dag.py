"""Replay prefix-bound GKR using public controls only; no source openings.

Requires trusted native prefix verification. This script does not itself replay
the native Poseidon transcript or authenticate the remaining PCS obligation.
"""
import gzip,hashlib,json
import pq384_terminal_gkr as g
from compile_swirl_fixed_dag import compile_air
from measure_swirl_rebalanced_gkr import merge
from swirl_consumer_weights import terminal_weights
from prove_swirl_weighted_dag import split_obligation
from prove_swirl_prefix_dag import BASE,PREFIX,OUT


def public_context(c=None, prefix_log=None, dag_path=None):
    if c is None:c=json.loads((PREFIX/'controls.json').read_text())
    if prefix_log is None:prefix_log=gzip.decompress((PREFIX/'transcript-log.txt.gz').read_bytes())
    dags={r['air']:r for r in map(json.loads,gzip.decompress((dag_path or BASE/'dag-export/dag.jsonl.gz').read_bytes()).splitlines())}
    records=[dags[t['air']] for t in c['traces']]
    controls=dict(lam=tuple(c['lambda']),beta=tuple(c['beta']),mu=tuple(c['mu']),
        eq_ns=[tuple(t['eq_ns']) for t in c['traces']],eq_sharp=[tuple(t['eq_sharp']) for t in c['traces']],
        norms=[tuple(t['norm']) for t in c['traces']],eq3bs=[[tuple(x) for x in t['eq3b']] for t in c['traces']])
    weights,offset=terminal_weights(records,**controls);flat=[w for row in weights for w in row]
    _,layout,slots=compile_air(merge(records),reassociate=True,public_weights=True,return_artifacts=True)
    traces={t['air']:t for t in c['traces']};known={}
    for key,index in slots.items():
        if key[0]=='output_weight':known[index]=flat[key[1]]
        elif key[0] in ('first_row','last_row','transition'):
            known[index]=tuple(traces[key[1]][{'first_row':'first','last_row':'last','transition':'transition'}[key[0]]])
        else:assert key[0]=='variable' and key[1] in (0,1)
    description=dict(profile='nearproof-opening-free-prefix-gkr-v1',
        prefix_log_sha384=hashlib.sha384(prefix_log).hexdigest(),controls=c)
    statement=hashlib.sha384(json.dumps(description,sort_keys=True,separators=(',',':')).encode()).digest()
    claim=g.sub(tuple(c['sumcheck_claim']),offset)
    return layout,slots,known,claim,statement,description


def main(proof=None, c=None, prefix_log=None, check_fixture=True, write_report=True, dag_path=None):
    layout,slots,known,claim,statement,description=public_context(c,prefix_log,dag_path)
    if proof is None:proof=json.loads(gzip.decompress((OUT/'proof.json.gz').read_bytes()))
    obligation=g.verify(layout,statement,proof,claim)
    residual=split_obligation(obligation,slots,known)
    if check_fixture:
        expected=json.loads(gzip.decompress((OUT/'pcs-obligation.json.gz').read_bytes()))
        assert json.loads(json.dumps(residual))==expected
    result=dict(status='OPENING_FREE_GKR_REPLAY_MATCHES_RESIDUAL',known_slots=len(known),pcs_coordinates=len(residual['coordinates']),
        scope='Uses trusted public prefix controls and fixed DAG. No witness nodes, column openings or source matrices read. PCS authentication of this new residual remains pending.')
    if write_report:
        (OUT/'opening-free-replay.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
    return residual, description, proof


if __name__=='__main__':main()
