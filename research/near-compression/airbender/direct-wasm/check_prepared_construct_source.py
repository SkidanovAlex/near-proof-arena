"""Exact first/last AST binding used by source-derived execution construction."""
import hashlib,json,subprocess,sys
from pathlib import Path
from prepared_function_air import air
root=Path(__file__).resolve().parents[2]
raw=subprocess.check_output(['lake','env','lean','--run','PreparedConstructExport.lean'],cwd=root)
formal=json.loads(raw);source=air()['tables'][0]['constraints'];indices=[453,454,455,456]
assert formal==[source[i] for i in indices]
report=dict(status='PASS',source_indices=indices,formal_json_sha256=hashlib.sha256(raw).hexdigest(),
    scope='Exact firstPC/firstSP/firstactive/lastDONE expressions; no initial-gas or final-output linkage asserted')
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
