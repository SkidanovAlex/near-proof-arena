"""Actual weighted evaluator versus independently folded Boolean-row residuals."""
import json
from pathlib import Path
import pq384_global_bus as bus


def fold(values,point):
    values=list(values)
    for r in point:
        values=[bus.add(a,bus.mul(r,bus.sub(b,a))) for a,b in zip(values[::2],values[1::2])]
    assert len(values)==1
    return values[0]


def main():
    package=Path(__file__).resolve().parents[2]
    directory=package/'results/pq384-code-table-long193'
    spec=json.loads((directory/'statement.json').read_text())['spec']
    n=3
    checks=0
    for ti,table in enumerate(spec['air']['tables']):
        layout=bus.aux.layout(table)
        width=table['width']
        rows=[[bus.base((r*r+3*c+r*c)%7) for c in range(width)]+
              [bus.ZERO]*(4*layout['aux_columns']) for r in range(1<<n)]
        finals=[bus.ONE]*layout['finals']
        alpha,gamma=bus.base(3),bus.base(5)
        residuals=[]
        points=[[bus.base((r>>i)&1) for i in range(n)] for r in range(1<<n)]
        for r,point in enumerate(points):
            current,nxt=rows[r],rows[(r+1)%(1<<n)]
            sels=bus.algebra.selectors(point)
            rs=[bus.algebra.eval_expr(e,current[:width],nxt[:width],spec['public'],sels)
                for e in bus.constraints(table)]
            rs+=bus.aux.evaluate(table,current[:width],nxt[:width],spec['public'],sels,alpha,gamma,
                                 bus.algebra.reconstruct(current[width:]),bus.algebra.reconstruct(nxt[width:]),finals)
            residuals.append(rs)
        for mixing in [bus.ZERO,bus.ONE,(2,3,5,7)]:
            batched=[]
            for rs in residuals:
                value=bus.ZERO
                for residual in reversed(rs):
                    value=bus.add(residual,bus.mul(mixing,value))
                batched.append(value)
            for tau in [[bus.ZERO]*n,[bus.ONE]*n,[(2,3,0,1),(5,0,2,0),(7,1,4,2)]]:
                actual=bus.ZERO
                for r,point in enumerate(points):
                    actual=bus.add(actual,bus.weighted(spec,ti,alpha,gamma,finals,mixing,tau,point,
                                                     rows[r],rows[(r+1)%(1<<n)]))
                assert actual==fold(batched,tau),(ti,mixing,tau)
                checks+=1
    report=dict(status='PASS',tables=2,synthetic_rows_per_table=8,target_checks=checks,
                scope='Actual literal table source/auxiliary residuals, cyclic next rows, power batching and equality weighting',
                limits=['Synthetic invalid traces; not proof verification',
                        'Parity check only; formal evaluator Boolean-row adapter remains explicit'])
    (directory/'weighted-target-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
