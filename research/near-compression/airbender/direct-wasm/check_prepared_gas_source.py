"""Check the formal gas/choice decomposition against the current Python AIR."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepared_function_air import air

root = Path(__file__).resolve().parents[2]
raw = subprocess.check_output(['lake','env','lean','--run',
                               'PreparedGasPublicBridgeExport.lean'], cwd=root)
formal = json.loads(raw)
source = air()['tables'][0]['constraints']
assert len(source) == 523 and len(formal) == 455
assert formal[:451] == source[:451]
assert formal[451:] == source[457:461]
middle, tail = source[451:457], source[461:]
assert source == formal[:451] + middle + formal[451:] + tail
report = {'status':'PASS','source_constraints':len(source),
          'formal_exprs':len(formal),'middle_count':len(middle),'tail_count':len(tail),
          'formal_json_sha256':hashlib.sha256(raw).hexdigest(),
          'scope':'Exact Expr syntax parity and decomposition; no Wasm/PREP authentication theorem'}
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
