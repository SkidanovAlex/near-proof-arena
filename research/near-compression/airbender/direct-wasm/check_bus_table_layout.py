"""Lean table allocation/order and residuals versus executable auxiliary evaluator."""
import json
from pathlib import Path
import subprocess
import pq384_global_bus as bus


def main():
    root=Path(__file__).resolve().parents[2]
    run=subprocess.run(['lake','env','lean','--run','BusTableLayoutExport.lean'],cwd=root,
                       check=True,capture_output=True,text=True)
    cases=json.loads(run.stdout)
    checks=trials=0
    for case in cases:
        profile=case['profile']
        table=dict(width=30,interactions=[dict(bus=2,send=p['send'],msg=[['v',j,0]],
                   mult=[['v',4+i,0] for i in range(p['bits'])]) for j,p in enumerate(profile)])
        layout=bus.aux.layout(table)
        assert case['chain_columns']==layout['chain_columns']
        offset=30;offsets=[]
        for p in profile:
            offsets.append(offset);offset+=2*max(0,p['bits']-1)
        assert case['offsets']==offsets
        assert case['accumulators']==list(range(offset,offset+len(profile)))
        for seed in [0,1,3,7]:
            current=[bus.base(seed+i) for i in range(30)]
            aux=[(seed+i,1,2,3) for i in range(layout['aux_columns'])]
            aux_next=[bus.add(v,bus.ONE) for v in aux]
            finals=[bus.base(7+j) for j in range(len(profile))]
            for selectors in [dict(first=bus.ONE,last=bus.ZERO,trans=bus.ONE),
                              dict(first=bus.ZERO,last=bus.ONE,trans=bus.ZERO),
                              dict(first=(1,2,3,4),last=(4,3,2,1),trans=(2,1,4,3))]:
                expected=bus.aux.evaluate(table,current,current,[],selectors,
                                          bus.ZERO,bus.base(5),aux,aux_next,finals)
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
                assert len(actual)==layout['chain_columns']+3*len(profile)
                assert actual==expected,(profile,seed,selectors)
                checks+=len(actual);trials+=1
    report=dict(status='PASS',profiles=len(cases),cases=trials,residual_comparisons=checks,
                scope='Lean-generated complete table layout, chains and stable send/receive boundary order',
                limits=['Synthetic source formulas with alpha=0; general fingerprint/source lowering remains',
                        'JSON parity test is not a proved Python/parser refinement',
                        'Executable Ext4; no executable Ext8 or cryptographic security certification'])
    (root/'results/bus-table-layout-parity.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
