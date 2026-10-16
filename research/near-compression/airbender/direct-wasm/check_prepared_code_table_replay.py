"""Compare the independent Python V2 evaluator with actual Lean source semantics.

The Lean adapter parses only test-generated JSON; it is not a proved wire codec.
"""
import argparse,json,sys
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--input',required=True);ap.add_argument('--lean-output',required=True);ap.add_argument('--report',required=True);args=ap.parse_args()
sys.path.insert(0,args.reference_dir)
from reference import inspect
cases=json.load(open(args.input));actual=json.load(open(args.lean_output));assert len(cases)==len(actual)
residual_count=message_count=0
for case,lean in zip(cases,actual):
    spec=case['spec'];expected=inspect(spec['air'],case['rows_by_table'],spec['public'])
    assert case['label']==lean['label']
    for key in ('residuals','interactions','public_messages'):
        assert lean[key]==expected[key],(case['label'],key)
    assert lean['public_fits']
    assert all(v==0 for table in lean['automatic_multiplicity_residuals'] for row in table for v in row)
    residual_count+=sum(len(row) for table in expected['residuals'] for row in table)
    message_count+=sum(len(row) for table in expected['interactions'] for row in table)
report=dict(status='PASS',cases=len(cases),exact_source_residuals=residual_count,
 exact_source_interactions=message_count,actual_source_functions=['Expr.eval','Interaction.multNat','Interaction.msgVal','pubMsgs','pubFit'],
 parser_proven_correct=False,cryptographic_verification=False)
Path(args.report).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
