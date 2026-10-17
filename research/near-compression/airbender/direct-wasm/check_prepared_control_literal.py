"""Exact whole-table Lean export parity, with explicit multiplicity constraints."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepared_control_air import air
from generate_prepared_control_literal import generate

root=Path(__file__).resolve().parents[2]
source=root/'NearCompression/PreparedControlLiteral.lean'
assert source.read_text()==generate(), 'generated module stale'
raw=subprocess.check_output(['lake','env','lean','--run','PreparedControlLiteralExport.lean'],cwd=root)
formal=json.loads(raw)
expected=air(11)
counts=[]
for table in expected['tables']:
    original=len(table['constraints'])
    automatic=[['*',e,['+',e,['-',['c',1]]]] for interaction in table['interactions'] for e in interaction['mult']]
    table['constraints']+=automatic
    counts.append(dict(user_constraints=original,automatic_constraints=len(automatic),total_constraints=len(table['constraints'])))
assert formal==expected, 'literal whole-table export mismatch'
report=dict(status='PASS',code_length=11,tables=counts,all_interactions_and_public_segments_equal=True,
            generated_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),export_sha256=hashlib.sha256(raw).hexdigest(),
            scope='Exact literal AST and executable export parity; supported semantic instantiation is separately proved, cryptographic soundness remains open')
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
