"""Native-control replay through GKR with proof-opening coordinate provenance.

Original proof is still required; this is not a compressed native verifier.
"""
import gzip,hashlib,json
from pathlib import Path
import pq384_terminal_gkr as g
from compile_swirl_fixed_dag import compile_air
from measure_swirl_rebalanced_gkr import merge
from swirl_consumer_weights import terminal_weights
from prove_swirl_weighted_dag import main,replay

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/native-dag-gkr'


def fixture(capture_path=None, openings_path=None, output_dir=OUT, dag_path=None):
    base=ROOT/'results/swirl-security-review'
    dags={r['air']:r for r in [json.loads(x) for x in gzip.decompress((dag_path or base/'dag-export/dag.jsonl.gz').read_bytes()).splitlines()]}
    capture_path = capture_path or base/'native-controls/capture.jsonl.gz'
    captures = gzip.decompress(capture_path.read_bytes()).splitlines()
    c=json.loads(captures[1] if len(captures)==3 else captures[0])
    assert len(captures) in (1,3)
    openings=json.loads(gzip.decompress((openings_path or OUT/'openings.json.gz').read_bytes()))
    assert [x['air'] for x in openings]==[x['air'] for x in c['traces']]
    by_air={x['air']:x for x in openings};records=[dags[t['air']] for t in c['traces']]
    controls=dict(lam=tuple(c['lambda']),beta=tuple(c['beta']),mu=tuple(c['mu']),
        eq_ns=[tuple(t['eq_ns']) for t in c['traces']],eq_sharp=[tuple(t['eq_sharp']) for t in c['traces']],
        norms=[tuple(t['norm']) for t in c['traces']],eq3bs=[[tuple(x) for x in t['eq3b']] for t in c['traces']])
    weights,offset=terminal_weights(records,**controls);flat=[w for row in weights for w in row]
    merged=merge(records);stats,layout,slots=compile_air(merged,reassociate=True,public_weights=True,return_artifacts=True)
    private=[g.ZERO]*layout['private_capacity'];seen={};checked=rotated=cached=0
    for record,trace in zip(records,c['traces']):
        opening=by_air[record['air']]
        for node,value in zip(record['nodes'],trace['nodes'],strict=True):
            op,*args=node
            if op=='variable':
                kind,part,rotation,column=args
                if kind==0:
                    assert opening['has_preprocessed'];part_index=1
                elif kind==1:
                    assert 0<=part<=opening['cached_count']
                    part_index=0 if part==opening['cached_count'] else 1+int(opening['has_preprocessed'])+part
                else:raise AssertionError('fixture has unexpected public/challenge variable')
                assert rotation in (0,1)
                assert rotation==0 or opening['need_rot']
                stride=2 if opening['need_rot'] else 1
                extracted=tuple(opening['parts'][part_index][stride*column+rotation])
                assert extracted==tuple(value),(record['air'],node)
                checked+=1;rotated+=rotation;cached+=int(kind==1 and part<opening['cached_count'])
                key=tuple(node+[record['air']]);v=extracted
            elif op in ('first_row','last_row','transition'):
                key=(op,record['air']);v=tuple(trace[{'first_row':'first','last_row':'last','transition':'transition'}[op]])
                assert v==tuple(value)
            else:continue
            if key in seen:assert seen[key]==v
            seen[key]=v;private[slots[key]]=v
    for key,index in slots.items():
        if key[0]=='output_weight':private[index]=flat[key[1]]
        else:assert key in seen
    claim=g.sub(tuple(c['sumcheck_claim']),offset)
    assert tuple(c['sumcheck_claim'])==tuple(c['evaluated_claim'])
    assert g.values(layout,private)[-1][layout['root']]==claim
    known={index:private[index] for key,index in slots.items() if not(key[0]=='variable' and key[1] in (0,1))}
    statement=hashlib.sha384(b'nearproof-native-weighted-v1'+json.dumps(c,sort_keys=True).encode()).digest()
    # This oversized diagnostic statement binds the original capture, including
    # openings via node evaluations. It is NOT a replacement compression transcript.
    output_dir.mkdir(parents=True,exist_ok=True)
    (output_dir/'coordinate-report.json').write_text(json.dumps(dict(checked=checked,rotated=rotated,cached=cached,
        trace_order=[x['air'] for x in openings],layout=stats),indent=2)+'\n')
    return stats,layout,slots,private,known,claim,statement


if __name__=='__main__':
    import sys
    if sys.argv[1:]==['--verify-saved']:replay(fixture,OUT)
    else:main(fixture,OUT,'Real accepted native controls and disclosed openings; original proof/capture still required.')
