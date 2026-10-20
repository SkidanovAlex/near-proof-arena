"""Compare literal authenticated CODE bus skeleton with executable AIR source."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepared_code_table_air import air

root = Path(__file__).resolve().parents[2]
raw = subprocess.check_output(['lake', 'env', 'lean', '--run',
                               'PreparedCodeBusExport.lean'], cwd=root)
formal = json.loads(raw)
source = air(193)
inactive = [source['tables'][1]['constraints'][437+i] for i in range(25)]
assert inactive == formal['inactive']
# The theorem accepts arbitrary execution constraints and one shared boundary
# expression list. These are the only parameters removed for this comparison.
exec_interactions = source['tables'][0]['interactions']
assert exec_interactions[0]['msg'] == exec_interactions[1]['msg']
for interaction in exec_interactions[:2]:
    interaction['msg'] = []
for table in source['tables']:
    table['constraints'] = []
automatic = 0
for table in formal['skeleton']['tables']:
    # Table.toJson appends the multiplicity-bit constraints required by
    # HoldsP.bits. These are separate from Table.constraints in Lean.
    expected = [['*', e, ['+', e, ['-', ['c', 1]]]]
                for interaction in table['interactions'] for e in interaction['mult']]
    assert table['constraints'] == expected
    automatic += len(expected)
    table['constraints'] = []
assert source == formal['skeleton']
report = dict(status='PASS', inactive_expressions=25, tables=2, interactions=5,
              public_segments=3, automatic_multiplicity_expressions=automatic,
              formal_json_sha256=hashlib.sha256(raw).hexdigest(),
              scope='Exact bus skeleton and inactive-count AST parity; arbitrary constraints and shared boundary are theorem parameters',
              limitations=['Not a verified exporter/parser or actual Wasm prepare-to-public CODE refinement'])
Path(sys.argv[1]).write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
