"""Native accepted-terminal capture versus exported DAG and weight interface.

Read-only instrumentation preserves native acceptance. This does not validate
an altered transcript, a PCS replacement, or quantum soundness.
"""
import gzip,hashlib,json
from pathlib import Path
import pq384_terminal_gkr as g
from swirl_consumer_weights import terminal_weights,direct_terminal
from prove_swirl_fixed_dag import dot

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/native-controls'


def main():
    source=ROOT/'results/swirl-security-review/dag-export/dag.jsonl.gz'
    dags={r['air']:r for r in [json.loads(x) for x in gzip.decompress(source.read_bytes()).splitlines()]}
    captures=[json.loads(x) for x in gzip.decompress((OUT/'capture.jsonl.gz').read_bytes()).splitlines()]
    matched=[];shapes=[]
    for number,c in enumerate(captures):
        traces=c['traces'];ids=[x['air'] for x in traces]
        shapes.append(dict(capture=number,airs=len(ids),nodes=sum(len(t['nodes']) for t in traces)))
        if set(ids)!=set(dags) or len(ids)!=len(dags):continue
        if any(len(t['nodes'])!=len(dags[t['air']]['nodes']) for t in traces):continue
        records=[dags[i] for i in ids]
        controls=dict(lam=tuple(c['lambda']),beta=tuple(c['beta']),mu=tuple(c['mu']),
                      eq_ns=[tuple(t['eq_ns']) for t in traces],eq_sharp=[tuple(t['eq_sharp']) for t in traces],
                      norms=[tuple(t['norm']) for t in traces],eq3bs=[[tuple(x) for x in t['eq3b']] for t in traces])
        values=[[tuple(x) for x in t['nodes']] for t in traces]
        checked=0
        for r,t,vs in zip(records,traces,values):
            for idx,(op,*args) in enumerate(r['nodes']):
                if op=='variable':continue # Coordinate-to-opening extraction is still separate.
                if op=='const':expected=g.base(args[0])
                elif op in ('first_row','last_row','transition'):
                    expected=tuple(t[{'first_row':'first','last_row':'last','transition':'transition'}[op]])
                elif op=='neg':expected=g.sub(g.ZERO,vs[args[0]])
                else:expected=g.gate(op,vs[args[0]],vs[args[1]])
                assert vs[idx]==expected,(number,r['air'],idx,op)
                checked+=1
        weights,offset=terminal_weights(records,**controls)
        weighted=offset
        for w,v in zip(weights,values):weighted=g.add(weighted,dot(w,v))
        direct=direct_terminal(records,values,**controls)
        assert weighted==direct==tuple(c['evaluated_claim'])==tuple(c['sumcheck_claim'])
        altered=dict(controls,mu=g.add(controls['mu'],g.ONE))
        wrong_weights,wrong_offset=terminal_weights(records,**altered)
        wrong=wrong_offset
        for w,v in zip(wrong_weights,values):wrong=g.add(wrong,dot(w,v))
        assert wrong!=weighted and offset!=g.ZERO and g.sub(weighted,offset)!=weighted
        matched.append(dict(capture=number,trace_air_order=ids,negative_checks=2,arithmetic_selector_nodes_checked=checked,
                            scalar=weighted,constant_offset=offset))
    assert matched,'No captured verifier shape matches exported fixed DAG'
    report=dict(status='NATIVE_TERMINAL_SCALAR_REPLAY_PASS',captures=shapes,matches=matched,
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,OUT/'capture.jsonl.gz',Path(__file__)]},
        limitations=['Variable values read from native node evaluation; source column/rotation extraction not yet cross-checked.',
                    'Native proof still discloses column openings and uses its original transcript.',
                    'No GKR-in-native-verifier, replacement PCS or QROM/PQ128 theorem.',
                    'Generic recursive fixture, not full NEAR.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
