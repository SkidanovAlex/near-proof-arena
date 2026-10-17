"""Semantic boundary/scaling tests; no claim of native proof or throughput tests."""
import json,subprocess,tempfile
from pathlib import Path
from collections import Counter
import prepared_code_table_air as lit
from prepared_function_air import eval_expr
from packed_byte_air import transform
ROOT=Path(__file__).resolve().parents[2]
def lean(file,*args):
    p=subprocess.run(['lake','env','lean','--run',file,*map(str,args)],cwd=ROOT,text=True,capture_output=True)
    if p.returncode:raise RuntimeError(p.stdout+'\n'+p.stderr)
    return json.loads(p.stdout)
# Fixtures come from actual prepare/step; a separate runCall oracle below checks
# final semantics without reading claimed outputs.
cases=lean('PreparedCodeTableFixture.lean')['cases']+lean('PreparedCodeTableFixture.lean','--edges')['cases']
for pairs in (127,128,256,512):cases+=lean('PreparedCodeTableFixture.lean','--pairs',pairs)['cases']
exports={};reports=[];rejected=[]
for case in cases:
    if case['label']=='stack-9':
        try:lit.make(case)
        except AssertionError:rejected.append(dict(label=case['label'],stage='witness generator',reason='eight-slot capacity'))
        else:raise AssertionError('nine-slot trace was accepted')
        continue
    old,rows=lit.make(case);spec,traces,packing=transform(old,rows)
    n=len(case['code'])
    if n not in exports:exports[n]=lean('PackedLiteralExport.lean',n)
    assert exports[n]==[old['air'],spec['air']]
    balance=Counter()
    for table,trace in zip(spec['air']['tables'],traces):
        for r,row in enumerate(trace):
            ev=lambda e:eval_expr(e,row,trace[(r+1)%len(trace)],spec['public'],r==0,r+1==len(trace))
            assert all(ev(e)==0 for e in table['constraints'])
            for i in table['interactions']:
                bits=[ev(e) for e in i['mult']];assert all(b in (0,1) for b in bits)
                balance[i['bus'],tuple(ev(e) for e in i['msg'])]+=sum(b<<k for k,b in enumerate(bits))*(1 if i['send'] else -1)
    pub=spec['public']
    for seg in spec['air']['pubSegs']:
        count=sum(pub[seg['countAt']+k]<<(8*k) for k in range(4))
        for j in range(count):
            start=seg['start']+seg['width']*j
            balance[seg['bus'],tuple(pub[start:start+seg['width']])]+=1 if seg['send'] else -1
    assert all(value==0 for value in balance.values())
    request={k:case[k] for k in ('wasm_bytes','method','prepaid')}
    with tempfile.TemporaryDirectory() as tmp:
        req=Path(tmp)/'request.json';req.write_text(json.dumps(request))
        inp=Path(tmp)/'input.json';inp.write_text(json.dumps(dict(request=request,public=pub)))
        eligible=lean('PreparedSliceCheck.lean',inp)
        assert eligible==dict(status='PASS',code_length=n)
        actual=lean('PreparedSliceOracle.lean',req,len(traces[0]))
    claimed=dict(done=pub[44]==1,failed=pub[45]==1,gas=sum(pub[46+k]<<(16*k) for k in range(4)),
        stack=[pub[50+2*k]+(pub[51+2*k]<<16) for k in range(pub[43])])
    assert actual==claimed
    reports.append(dict(label=case['label'],code_length=n,exec_rows=len(traces[0]),code_rows=len(traces[1]),
        range_rows=len(traces[2]),range_lookups=packing['range_lookups'],max_range_multiplicity=packing['max_range_multiplicity'],failed=actual['failed']))
    print('PASS '+case['label'],file=__import__('sys').stderr,flush=True)
assert any(r['range_rows']>256 for r in reports)
assert any(r['failed'] for r in reports)
print(json.dumps(dict(status='PASS',cases=reports,rejected=rejected,
    scope='Actual Lean preparation/step fixtures, full polynomial and exact natural-bus checks, family AIR export equality, eligibility and independent runCall parity. No new native proofs or performance/security claims.'),indent=2))
