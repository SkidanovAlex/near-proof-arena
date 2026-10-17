"""Compare fixed wiring interpolation to direct GKR wiring at fresh points."""
import itertools,json,random
from pathlib import Path
from compile_swirl_gkr_verifier import Circuit,main,OUT
import pq384_terminal_gkr as g
from swirl_wiring_bdd import wiring


def check():
    rng=random.Random(20261020);cases=0
    for n,m in [(0,0),(1,1),(2,3),(3,2)]:
        gates=[(rng.choice(['add','sub','mul']),rng.randrange(1<<m),rng.randrange(1<<m)) for _ in range(1<<n)]
        for kind in ['output_first','inputs_first']+[f'interleaved_{p}{s}' for p in ['012','021','102','120','201','210'] for s in ['', '_high']]:
            c=Circuit();names=[f'x/{i}' for i in range(2*n+2*m+3)]
            xs=[c.inp(x) for x in names];q1=xs[:n];q2=xs[n:2*n]
            ru=xs[2*n:2*n+m];rv=xs[2*n+m:2*n+2*m];scale,a,b=xs[-3:]
            node=wiring(c,gates,[(q1,c.one),(q2,scale)],ru,rv,a,b,kind)
            for mode in ['zero','one','random']:
                values=[g.ZERO if mode=='zero' else g.ONE if mode=='one' else tuple(rng.randrange(2013265921) for _ in range(4)) for _ in names]
                result=c.evaluate(dict(zip(names,values)))[node]
                weights=g.output_weights(len(gates),[(values[:n],g.ONE),(values[n:2*n],values[-3])])
                direct=g.wiring(gates,weights,values[2*n:2*n+m],values[2*n+m:2*n+2*m],values[-2],values[-1])
                assert result==direct;cases+=1
    out=OUT.parent/'bdd-gkr-verifier';out.mkdir(exist_ok=True)
    (out/'small-parity.json').write_text(json.dumps(dict(cases=cases,seed=20261020))+'\n')
    main('interleaved_012_high',out)


if __name__=='__main__':check()
