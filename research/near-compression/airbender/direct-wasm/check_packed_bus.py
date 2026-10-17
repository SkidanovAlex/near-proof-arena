"""Validate complete interaction pairings and range-only added traffic."""
import copy,json,subprocess,tempfile
from pathlib import Path
import prepared_code_table_air as lit
ROOT=Path(__file__).resolve().parents[2]
source=ROOT/'results/native-literal-byte-packed-input'
old,_=lit.make(json.loads((source/'fixture.json').read_text()))
packed=json.loads((source/'spec.json').read_text())
tasks=[]
for ti in range(2):
    xs=old['air']['tables'][ti]['interactions'];ys=packed['air']['tables'][ti]['interactions']
    tasks.append(dict(table=ti,source=xs,target=ys[:len(xs)]))
    assert all(i['bus']==4 for i in ys[len(xs):])
assert len(old['air']['tables'])==2 and len(packed['air']['tables'])==3
assert all(i['bus']==4 for i in packed['air']['tables'][2]['interactions'])
assert old['air']['pubSegs']==packed['air']['pubSegs']
assert all(i['bus']!=4 for t in old['air']['tables'] for i in t['interactions'])
assert all(seg['bus']!=4 for seg in old['air']['pubSegs'])
negative=[]
for field,value in [('bus',4),('send',False),('msg',[['c',0]]),('mult',[['c',0]])]:
    task=copy.deepcopy(tasks[0]);task['target'][0][field]=value;negative.append(task)
for mutate in ('drop','duplicate'):
    task=copy.deepcopy(tasks[0])
    if mutate=='drop':task['target'].pop()
    else:task['target'].append(task['target'][-1])
    negative.append(task)
with tempfile.TemporaryDirectory() as tmp:
    path=Path(tmp)/'pairs.json';path.write_text(json.dumps(tasks+negative))
    run=subprocess.run(['lake','env','lean','--run','PackedBusCheck.lean',str(path)],cwd=ROOT,text=True,capture_output=True,check=True)
assert json.loads(run.stdout)==[True,True]+[False]*len(negative)
print(json.dumps(dict(status='PASS',paired_interactions=sum(len(t['source']) for t in tasks),negative_pairings_rejected=len(negative),
    public_segments_unchanged=True,added_traffic_only_bus=4,
    scope='Executable pairing checks use a kernel-proved checker; universal natural-count and global two-table preservation proved. Full concrete HoldsP transfer remains to be assembled.'),indent=2))
