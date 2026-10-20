"""Check packed AIR constraints/buses and an isolated invalid-byte witness."""
import sys as _sys;from pathlib import Path as _P;_sys.path.insert(0,str(_P(__file__).resolve().parents[2]/'native'));import native_paths
from pathlib import Path
from collections import Counter
import copy,json,os,struct,subprocess,tempfile
import prepared_code_table_air as lit
from prepared_function_air import eval_expr,P
from packed_byte_air import transform
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/native-literal-byte-packed'
case=json.loads((OUT/'fixture.json').read_text());old,rows=lit.make(case)
spec,packed,packing=transform(old,rows)
assert spec==json.loads((OUT/'spec.json').read_text()) and spec['public']==old['public']
def check_constraints(traces):
    for table,trace in zip(spec['air']['tables'],traces):
        for i,row in enumerate(trace):
            for e in table['constraints']:assert eval_expr(e,row,trace[(i+1)%len(trace)],spec['public'],i==0,i+1==len(trace))==0

def balances(traces):
    counts=Counter()
    for table,trace in zip(spec['air']['tables'],traces):
        for i,row in enumerate(trace):
            ev=lambda e:eval_expr(e,row,trace[(i+1)%len(trace)],spec['public'],i==0,i+1==len(trace))
            for interaction in table['interactions']:
                bs=[ev(e) for e in interaction['mult']];assert all(b in (0,1) for b in bs)
                count=sum(b<<j for j,b in enumerate(bs))
                counts[interaction['bus'],tuple(ev(e) for e in interaction['msg'])]+=count*(1 if interaction['send'] else -1)
    pub=spec['public']
    for segment in spec['air']['pubSegs']:
        count=sum(pub[segment['countAt']+i]<<(8*i) for i in range(4))
        for j in range(count):
            start=segment['start']+j*segment['width'];msg=tuple(pub[start:start+segment['width']])
            counts[segment['bus'],msg]+=1 if segment['send'] else -1
    return {k:v for k,v in counts.items() if v}
check_constraints(packed);assert not balances(packed)
bad=copy.deepcopy(packed);assert bad[0][0][43:45]==[0,0]
bad[0][0][43:45]=[P-256,1]
check_constraints(bad)
unbalanced=balances(bad);assert unbalanced and all(bus==4 for bus,_ in unbalanced)
# Run the actual proving path. Its NonZeroRootSum guard rejects before a proof
# is produced; report this accurately, not as a forged-proof verifier test.
with tempfile.TemporaryDirectory(prefix='nearproof-invalid-byte-') as tmp:
    tmp=Path(tmp)
    for i,trace in enumerate(bad):(tmp/f'rows-{i}.bin').write_bytes(b''.join(struct.pack('<I',v) for row in trace for v in row))
    (tmp/'public.bin').write_bytes((OUT/'public.bin').read_bytes())
    env=dict(os.environ,NEARPROOF_LITERAL_OUT=str(tmp),NEARPROOF_N_STACK='15',NEARPROOF_ALL_LIST='1',NEARPROOF_LOG_BLOWUP='7',NEARPROOF_INTERACTION_LOG='26',NEARPROOF_QUERY_BITS='268',RAYON_NUM_THREADS='4')
    for key in ['NEARPROOF_REPLAY','NEARPROOF_DICTIONARY','NEARPROOF_TRANSCRIPT_VECTORS','NEARPROOF_EXPECT_RANGE_REJECTION']:env.pop(key,None)
    run=subprocess.run(['cargo','run','--locked','--manifest-path',str(native_paths.CRATE/'Cargo.toml'),'--release'],env=env,text=True,capture_output=True)
    assert run.returncode!=0 and 'LogupZerocheck(NonZeroRootSum)' in run.stderr
    assert not (tmp/'child.proof').exists()
(OUT/'invalid-byte.log').write_text(run.stdout+run.stderr)
report=dict(packing=packing,all_honest_row_constraints_pass=True,all_honest_integer_buses_balance=True,
    invalid_byte=P-256,preserved_all_polynomial_constraints=True,only_bus4_unbalanced=True,
    invalid_range_bus_residuals=[dict(value=message[0],count=count) for (_,message),count in sorted(unbalanced.items())],
    invalid_prover_rejected='LogupZerocheck(NonZeroRootSum)',invalid_proof_generated=False,
    formal_refinement_proved=False,scope='Concrete transformation/witness checks, not universal AIR soundness or Rust refinement.')
(OUT/'packing-check.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
