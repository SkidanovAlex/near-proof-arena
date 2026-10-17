"""Compare Lean addition carry expressions with the executable AIR."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepared_function_air import air

root=Path(__file__).resolve().parents[2]
raw=subprocess.check_output(['lake','env','lean','--run','PreparedOperandExport.lean'],cwd=root)
formal=json.loads(raw)
source=air()['tables'][0]['constraints']
assert len(formal)==2 and formal==source[489:491]
report={'status':'PASS','source_constraint_indices':[489,490],
        'formal_json_sha256':hashlib.sha256(raw).hexdigest(),
        'scope':'Exact two-limb gated carry Expr syntax; full transition composition remains separate'}
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
