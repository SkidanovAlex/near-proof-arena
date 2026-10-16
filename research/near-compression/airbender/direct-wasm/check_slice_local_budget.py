"""Initial constraint batching/row-weighting budget, before adaptive sumcheck."""
import json
import math
from pathlib import Path
import pq384_global_bus as bus


def main():
    root=Path(__file__).resolve().parents[2]
    directory=root/'results/pq384-code-table-long193'
    spec=json.loads((directory/'statement.json').read_text())['spec']
    tables=[]
    for index,(table,n) in enumerate(zip(spec['air']['tables'],spec['log_rows'])):
        layout=bus.aux.layout(table)
        selectors=bus.algebra.selectors([bus.ZERO]*n)
        current=[bus.ZERO]*table['width']
        current[0]=bus.base(2)  # Deliberately violates a literal Boolean constraint.
        nxt=[bus.ZERO]*table['width']
        originals=[bus.algebra.eval_expr(e,current,nxt,spec['public'],selectors)
                   for e in bus.constraints(table)]
        auxiliary=bus.aux.evaluate(table,current,nxt,spec['public'],selectors,bus.base(3),bus.base(5),
                                  [bus.ZERO]*layout['aux_columns'],[bus.ZERO]*layout['aux_columns'],
                                  [bus.ONE]*layout['finals'])
        residuals=originals+auxiliary
        assert any(v!=bus.ZERO for v in originals)
        L=len(residuals)
        # The expression in the Lean theorem normalizes to (L-1+n)/|K|.
        numerator=L-1+n
        tables.append(dict(table=index,log_rows=n,source_residuals=len(originals),
                           auxiliary_residuals=len(auxiliary),total_residuals=L,
                           invalid_row_nonzero_residuals=sum(v!=bus.ZERO for v in residuals),
                           initial_error_numerator=numerator,
                           ideal_ext4_bits=math.log2(bus.P**4)-math.log2(numerator),
                           ideal_ext8_bits=math.log2(bus.P**8)-math.log2(numerator)))
    report=dict(status='CONDITIONAL_COMPONENT_BOUND',tables=tables,
                theorem='NearCompression.air_residual_batch_zero_count',
                limits=['Fixed residual matrix before mixing and row point; source and auxiliaries must be bound',
                        'Independent uniform challenges only; executable profile remains Q8/Ext4',
                        'Actual all-row residual/equality-weight adapter, adaptive sumcheck, PCS and QROM still required'])
    (directory/'local-initial-budget.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
