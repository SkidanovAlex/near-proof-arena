"""Check theorem-backed range AIR and receiver isolation against actual spec."""
import json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
spec=json.loads((ROOT/'results/native-literal-byte-packed-input/spec.json').read_text())
run=subprocess.run(['lake','env','lean','--run','PackedRangeExport.lean'],cwd=ROOT,text=True,capture_output=True,check=True)
table,exec_sends,code_sends=json.loads(run.stdout)
assert table==spec['air']['tables'][2]
assert len(spec['air']['tables'])==3
assert all(seg['bus']!=4 for seg in spec['air']['pubSegs'])
receivers=[]
for ti,t in enumerate(spec['air']['tables']):
    for interaction in t['interactions']:
        if interaction['bus']==4 and not interaction['send']:receivers.append((ti,interaction))
assert receivers==[(2,table['interactions'][0])]
for ti,senders in enumerate([exec_sends,code_sends]):
    actual=[i for i in spec['air']['tables'][ti]['interactions'] if i['bus']==4]
    assert actual==senders
print(json.dumps(dict(status='PASS',receiver_table=2,range_constraints=len(table['constraints']),
    sender_counts=[len(exec_sends),len(code_sends)],public_range_segments=0,
    scope='Exact theorem-backed range AST and isolation/sender checks. HoldsP-to-range theorem kernel-proved; native acceptance-to-HoldsP and whole AIR refinement remain open.'),indent=2))
