"""Exact AST comparison for every CODE-order theorem source membership premise."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepared_code_table_air import code_table

root = Path(__file__).resolve().parents[2]
raw = subprocess.check_output(['lake', 'env', 'lean', '--run',
                               'PreparedCodeOrderExport.lean'], cwd=root)
formal = json.loads(raw)
source = code_table()['constraints']
indices = list(range(198)) + [199+2*i for i in range(32)] + [263, 264, 265]
assert len(formal) == len(indices)
assert formal == [source[i] for i in indices]
report = dict(status='PASS', formal_expressions=len(formal), indices=indices,
              formal_json_sha256=hashlib.sha256(raw).hexdigest(),
              scope='Exact CODE-order source AST parity; no verified parser or full execution refinement')
Path(sys.argv[1]).write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
