"""Exact source binding for the Lean successful-add transition subset."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepared_function_air import air

root=Path(__file__).resolve().parents[2]
raw=subprocess.check_output(['lake','env','lean','--run','PreparedAddTransitionExport.lean'],cwd=root)
formal=json.loads(raw);source=air()['tables'][0]['constraints']
indices=list(range(463,481))+list(range(492,523,2))
assert len(formal)==34 and formal==[source[i] for i in indices]
# Instantiate the theorem's prefix, middle and interleaved dead-slot context.
interleaved=[]
for i,step in enumerate(formal[18:]):interleaved.extend([source[491+2*i],step])
assert source==source[:463]+formal[:18]+source[481:491]+interleaved
report={'status':'PASS','source_constraints':len(source),'formal_expressions':len(formal),
        'indices':indices,'full_source_decomposition':True,
        'formal_json_sha256':hashlib.sha256(raw).hexdigest(),
        'scope':'Exact Expr parity; successful-add theorem retains active/opcode/row-choice premises'}
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
