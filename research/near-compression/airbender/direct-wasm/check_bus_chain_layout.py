"""Generated Lean chain formulas versus actual Python auxiliary residuals."""
import json
from pathlib import Path
import subprocess
import pq384_global_bus as bus


def main():
    root=Path(__file__).resolve().parents[2]
    run=subprocess.run(['lake','env','lean','--run','BusChainLayoutExport.lean'],cwd=root,
                       check=True,capture_output=True,text=True)
    cases=json.loads(run.stdout)
    checks=0
    for case in cases:
        k=case['tail_bits'];width=2+k
        table=dict(width=width,interactions=[dict(bus=2,send=True,msg=[['v',0,0]],
                   mult=[['v',i,0] for i in range(1,width)])])
        for seed in [0,1,7]:
            current=[bus.base(seed+2),bus.ONE]+[bus.base((seed+i)%3) for i in range(k)]
            aux=[(seed+i,1,2,3) for i in range(2*k)]+[bus.ONE]
            expected=bus.aux.evaluate(table,current,current,[],dict(first=bus.ONE,last=bus.ZERO,trans=bus.ONE),
                                      bus.ZERO,bus.base(5),aux,aux,[bus.ONE])[:2*k]
            inputs=current+aux
            def ev(e):
                if e[0]=='c':
                    assert all(v==0 for v in e[1][1:])
                    return bus.base(e[1][0])
                if e[0]=='v':return inputs[e[1]]
                a,b=ev(e[1]),ev(e[2])
                return {'+':bus.add,'-':bus.sub,'*':bus.mul}[e[0]](a,b)
            actual=[ev(e) for e in case['residuals']]
            assert len(actual)==2*k and actual==expected,(k,seed)
            checks+=len(actual)
    report=dict(status='PASS',tail_bit_lengths=[0,1,24],cases=9,residual_comparisons=checks,
                scope='Actual Lean-generated square/link chains in Python evaluator order',
                limits=['Chain only; full interaction/boundary layout certification remains',
                        'JSON parity test is not a proved Python/parser refinement'])
    (root/'results/bus-chain-layout-parity.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
