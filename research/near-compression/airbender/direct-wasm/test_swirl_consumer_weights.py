"""Algebraic interface tests, not a transcript/native-verifier integration."""
import copy
import gzip
import hashlib
import json
import random
from pathlib import Path
import pq384_terminal_gkr as g
from swirl_consumer_weights import terminal_weights,direct_terminal

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/consumer-weights'


def main():
    path=ROOT/'results/swirl-security-review/dag-export/dag.jsonl.gz'
    original=[json.loads(x) for x in gzip.decompress(path.read_bytes()).splitlines()]
    rng=random.Random(20261017)
    def rand():return tuple(rng.randrange(2013265921) for _ in range(4))
    checks=offset_checks=0
    for ordering in (original,list(reversed(original))):
        n=len(ordering)
        for mode in ('random','zero','one'):
            controls=dict(lam=rand(),beta=rand(),mu=rand(),eq_ns=[rand() for _ in range(n)],
                          eq_sharp=[rand() for _ in range(n)],norms=[rand() for _ in range(n)],
                          eq3bs=[[rand() for _ in r['interactions']] for r in ordering])
            if mode!='random':
                for k in ('lam','beta','mu'):controls[k]=g.ZERO if mode=='zero' else g.ONE
            values=[[rand() for _ in r['nodes']] for r in ordering]
            weights,constant=terminal_weights(ordering,**controls)
            claimed=constant
            for ws,vs in zip(weights,values):
                for w,v in zip(ws,vs):claimed=g.add(claimed,g.mul(w,v))
            expected=direct_terminal(ordering,values,**controls)
            assert claimed==expected;checks+=1
            if constant!=g.ZERO:
                assert g.sub(claimed,constant)!=expected;offset_checks+=1
    rejected=0
    for mutation in ('controls','interaction','node','bus'):
        bad=copy.deepcopy(original);args=copy.deepcopy(controls)
        # Use matching forward order controls for shape tests.
        args['eq3bs']=[[rand() for _ in r['interactions']] for r in bad]
        if mutation=='controls':args['eq_ns'].pop()
        elif mutation=='interaction':args['eq3bs'][0].append(g.ONE)
        elif mutation=='node':bad[0]['constraints'][0]=len(bad[0]['nodes'])
        else:
            r=next(r for r in bad if r['interactions']);r['interactions'][0]['bus']=65536
        try:terminal_weights(bad,**args)
        except ValueError:rejected+=1
        else:raise AssertionError(mutation)
    from compile_swirl_fixed_dag import compile_air
    from measure_swirl_rebalanced_gkr import merge
    layout=compile_air(merge(original),reassociate=True,public_weights=True)
    assert layout['inputs']==2373+3871 and layout['gkr_field_elements']==1264
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'layout.json').write_text(json.dumps(layout,indent=2)+'\n')
    sources=[path,Path(__file__),Path(__file__).with_name('swirl_consumer_weights.py'),Path(__file__).with_name('compile_swirl_fixed_dag.py')]
    report=dict(status='TERMINAL_SCALAR_IDENTITY_CHECKED',cases=checks,nonzero_offset_checks=offset_checks,
        malformed_rejected=rejected,airs=len(original),
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        limitations=['Controls supplied, not derived from actual proof transcript.',
                    'Trace order supplied; real trace/AIR permutation binding remains required.',
                    'Tested arbitrary Ext4 node values; not native verifier acceptance.',
                    'No PCS input proof, GKR integration, Lean theorem, PQ128 or NEAR proof.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
