"""Bind remaining TableLocal add/gas/status expressions to frozen source AIR."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepared_function_air import air

root=Path(__file__).resolve().parents[2]
raw=subprocess.check_output(['lake','env','lean','--run','PreparedAddTableLocalExport.lean'],cwd=root)
formal=json.loads(raw);source=air()['tables'][0]['constraints']
indices=[451,461,462,482,485,486,487,488]
assert len(formal)==len(indices) and formal==[source[i] for i in indices]
report={'status':'PASS','formal_expressions':len(formal),'indices':indices,
        'formal_json_sha256':hashlib.sha256(raw).hexdigest(),
        'scope':'Exact source parity for TableLocal add composition; public CODE provenance remains external'}
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
