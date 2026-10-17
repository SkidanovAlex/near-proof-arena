"""Actual literal slice descriptors lowered by Lean versus executable auxiliaries."""
import json
from pathlib import Path
import subprocess
import pq384_global_bus as bus
from prepared_code_table_air import air


def main():
    root=Path(__file__).resolve().parents[2]
    fixture=root/'results/pq384-code-table-long193/statement.json'
    spec=json.loads(fixture.read_text())['spec']
    assert spec['air']==air(193)
    run=subprocess.run(['lake','env','lean','--run','PreparedSliceAuxLayoutExport.lean',str(fixture)],
                       cwd=root,check=True,capture_output=True,text=True)
    cases=json.loads(run.stdout)
    checks=trials=0
    counts={}
    for case in cases:
        table=spec['air']['tables'][case['table']]
        layout=bus.aux.layout(table)
        assert case['chain_columns']==layout['chain_columns']
        counts[case['table']]=len(case['residuals'])
        for seed in [0,1,7]:
            current=[(seed+i,1,2,3) for i in range(table['width'])]
            next_source=[bus.add(v,bus.ONE) for v in current]
            aux=[(seed+i,3,2,1) for i in range(layout['aux_columns'])]
            aux_next=[bus.add(v,bus.ONE) for v in aux]
            finals=[bus.base(7+j) for j in range(layout['finals'])]
            for selectors in [dict(first=bus.ONE,last=bus.ZERO,trans=bus.ONE),
                              dict(first=bus.ZERO,last=bus.ONE,trans=bus.ZERO),
                              dict(first=(1,2,3,4),last=(4,3,2,1),trans=(2,1,4,3))]:
                expected=bus.aux.evaluate(table,current,next_source,spec['public'],selectors,
                                          bus.base(case['alpha']),bus.base(5),aux,aux_next,finals)
                inputs=current+aux;nxt=next_source+aux_next
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
                assert len(actual)==layout['chain_columns']+3*layout['finals']
                assert actual==expected,(case['table'],case['alpha'],seed,selectors)
                checks+=len(actual);trials+=1
    report=dict(status='PASS',tables=counts,alphas=[0,1,7],cases=trials,residual_comparisons=checks,
                scope='Actual preparedLiteralAir(193) lowered and allocated in Lean; all auxiliary residuals versus Python',
                limits=['Finite parity evidence is not a proved Python/parser refinement',
                        'Base-field challenges and Ext4 values; no executable Ext8 certification',
                        'No commitment extraction or end-to-end soundness claim'])
    (root/'results/pq384-code-table-long193/aux-layout-parity.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
