"""Compare Lean AST degree bounds with actual literal verifier profiles."""
import json
from pathlib import Path
import subprocess
import pq384_global_bus as bus


def main():
    root=Path(__file__).resolve().parents[2]
    fixture=root/'results/pq384-code-table-long193/statement.json'
    spec=json.loads(fixture.read_text())['spec']
    run=subprocess.run(['lake','env','lean','--run','PreparedSliceDegreeExport.lean',str(fixture)],
                       cwd=root,check=True,capture_output=True,text=True)
    cases=json.loads(run.stdout)
    reports=[]
    for case in cases:
        t=case['table'];table=spec['air']['tables'][t]
        degree=bus.algebra.table_degree(table,spec['air']['numPub'])
        source_max=max(case['source_degrees'],default=0)
        aux_max=max(case['auxiliary_degrees'],default=0)
        assert max(source_max,aux_max)<=degree,(t,source_max,aux_max,degree)
        assert len(case['auxiliary_degrees'])==bus.aux.layout(table)['chain_columns']+3*len(table['interactions'])
        reports.append(dict(table=t,alpha=case['alpha'],source_residuals=len(case['source_degrees']),
                            auxiliary_residuals=len(case['auxiliary_degrees']),source_degree=source_max,
                            auxiliary_degree=aux_max,verifier_residual_degree=degree,
                            weighted_round_degree=degree+1,round_coefficients=degree+2,
                            conditional_rounds_numerator=(degree+1)*spec['log_rows'][t]))
    report=dict(status='PASS',cases=reports,scope='Actual literal source and generated auxiliary formula degrees',
                limits=['Computed AST bounds for retained fixture; no universal parser refinement',
                        'Affine coordinate-slice representation and terminal PCS authentication remain open',
                        'Conditional round numerators are not whole-protocol security'])
    (root/'results/pq384-code-table-long193/combined-degree-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
