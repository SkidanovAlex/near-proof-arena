"""Compare every original column against the actual generator's packing map."""
import json,subprocess
from pathlib import Path
import prepared_code_table_air as lit
from packed_byte_air import column_layout
ROOT=Path(__file__).resolve().parents[2]
regions=[[(lit.STACK,256),(lit.GAS,64),(lit.DIFF,64),(lit.RESULT,32),(lit.IMM,32),(lit.FEE,64)],[(lit.CIMM,32),(lit.CFEE,64)]]
expected=[]
for width,groups in zip([lit.WIDTH,lit.CWIDTH],regions):
    removed,mapping,bytecols,new_width=column_layout(width,groups)
    slots=[None]*width
    for old,new in mapping.items():slots[old]=[0,new,0]
    for old,new in bytecols.items():
        for bit in range(8):slots[old+bit]=[1,new,bit]
    assert all(slot is not None for slot in slots)
    assert all(slot[1]<new_width for slot in slots)
    expected.append(slots)
run=subprocess.run(['lake','env','lean','--run','PackedLayoutExport.lean'],cwd=ROOT,text=True,capture_output=True,check=True)
assert json.loads(run.stdout)==expected
print(json.dumps(dict(status='PASS',columns=[len(t) for t in expected],
    bit_columns=sum(s[0] for t in expected for s in t),
    scope='Exact Lean/generated layout equality; macro consistency kernel-proved, whole AIR implication still pending.'),indent=2))
