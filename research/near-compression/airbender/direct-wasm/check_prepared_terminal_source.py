"""Exact source syntax for successful end's stack-depth requirement."""
import hashlib,json,subprocess,sys
from pathlib import Path
from prepared_function_air import air

root=Path(__file__).resolve().parents[2]
raw=subprocess.check_output(['lake','env','lean','--run','PreparedTerminalExport.lean'],cwd=root)
assert json.loads(raw)==air()['tables'][0]['constraints'][484]
report={'status':'PASS','source_index':484,'formal_json_sha256':hashlib.sha256(raw).hexdigest(),
        'scope':'Exact source AST; actual gas burn/sync and Wasm call boundary remain separate'}
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
