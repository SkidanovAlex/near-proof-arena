"""Conditional initial-batching plus adaptive-sumcheck budget for the slice."""
import json
from pathlib import Path


def main():
    root=Path(__file__).resolve().parents[2]
    fixture=root/'results/pq384-code-table-long193'
    spec=json.loads((fixture/'statement.json').read_text())['spec']
    degrees=json.loads((fixture/'combined-degree-report.json').read_text())
    assert degrees['status']=='PASS'
    tables=[]
    for t,rounds in enumerate(spec['log_rows']):
        cases=[c for c in degrees['cases'] if c['table']==t]
        assert cases
        c=cases[0]
        shape=lambda x:(x['source_residuals'],x['auxiliary_residuals'],x['weighted_round_degree'])
        assert all(shape(x)==shape(c) for x in cases)
        residuals=c['source_residuals']+c['auxiliary_residuals']
        initial=residuals-1+rounds
        adaptive=c['weighted_round_degree']*rounds
        tables.append(dict(table=t,residuals=residuals,rounds=rounds,
                           initial_numerator=initial,adaptive_numerator=adaptive,
                           composed_numerator=initial+adaptive))
    report=dict(status='CONDITIONAL_COMPONENT_BOUND',theorem='NearCompression.air_local_invalid_trace_count',
                tables=tables,formula='(residual_count-1+row_log+round_degree*row_log)/field_size',
                premises=['One fixed invalid source/auxiliary trace before mixing and equality-point challenges',
                          'Initial claim zero, checked degree/endpoint/update messages',
                          'Terminal equality to the actual trace evaluator',
                          'Independent ideal challenges from a distinct sample'],
                exclusions=['Terminal PCS authentication and common-trace extraction',
                            'Global bus and multi-table transcript composition',
                            'Fiat-Shamir/quantum security and total secure proof bytes'])
    (fixture/'local-composed-budget.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
