"""Lean-generated full interaction residuals versus executable evaluator."""
import json
from pathlib import Path
import subprocess
import pq384_global_bus as bus


def main():
    root=Path(__file__).resolve().parents[2]
    run=subprocess.run(['lake','env','lean','--run','BusInteractionLayoutExport.lean'],cwd=root,
                       check=True,capture_output=True,text=True)
    cases=json.loads(run.stdout)
    checks=trials=0
    for case in cases:
        n=case['bits'];width=1+n;k=max(0,n-1)
        table=dict(width=width,interactions=[dict(bus=2,send=True,msg=[['v',0,0]],
                   mult=[['v',i,0] for i in range(1,width)])])
        for seed in [0,1,3,7]:
            current=[bus.base(seed+2)]+[bus.base((seed+i)%3) for i in range(n)]
            aux=[(seed+i,1,2,3) for i in range(2*k)]+[bus.base(seed+1)]
            aux_next=[bus.add(v,bus.ONE) for v in aux]
            for selectors in [dict(first=bus.ONE,last=bus.ZERO,trans=bus.ONE),
                              dict(first=bus.ZERO,last=bus.ONE,trans=bus.ZERO),
                              dict(first=(1,2,3,4),last=(4,3,2,1),trans=(2,1,4,3))]:
                expected=bus.aux.evaluate(table,current,current,[],selectors,
                                          bus.ZERO,bus.base(5),aux,aux_next,[bus.base(7)])
                inputs=current+aux;nxt=current+aux_next
                def ev(e):
                    if e[0]=='c':
                        assert all(v==0 for v in e[1][1:])
                        return bus.base(e[1][0])
                    if e[0]=='v':return inputs[e[1]]
                    if e[0]=='next':return nxt[e[1]]
                    if e[0] in selectors:return selectors[e[0]]
                    a,b=ev(e[1]),ev(e[2])
                    return {'+':bus.add,'-':bus.sub,'*':bus.mul}[e[0]](a,b)
                actual=[ev(e) for e in case['residuals']]
                assert len(actual)==2*k+3 and actual==expected,(n,seed,selectors)
                checks+=len(actual);trials+=1
    report=dict(status='PASS',bit_lengths=[0,1,2,25],cases=trials,residual_comparisons=checks,
                scope='Lean-generated interaction chain and boundary residuals; arbitrary selectors, nonboolean bits, zero fingerprint',
                limits=['Single interaction; table allocation/order and fingerprint lowering remain',
                        'JSON parity test is not a proved Python/parser refinement',
                        'Executable uses Ext4; generic field theorem does not certify executable Ext8'])
    (root/'results/bus-interaction-layout-parity.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
