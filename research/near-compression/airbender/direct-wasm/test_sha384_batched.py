"""Independent AST/routing checks and full diagnostic proof verification."""
import argparse,collections,copy,hashlib,json,sys,time
from pathlib import Path
from prepare_sha384_batched import public_tape,metadata

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--proof-directory',required=True);p.add_argument('--message',required=True);a=p.parse_args()
    sys.path.append(a.reference_dir);sys.path.append(str(Path(a.reference_dir).parent/'generic-air'))
    import reference as ref
    import pq384_global_bus as bus
    import pq384_global_bus_codec as codec
    src=Path(a.fixture_directory);out=Path(a.proof_directory);message=Path(a.message).read_bytes();canonical=json.loads((src/'spec.json').read_text());statement=json.loads((out/'statement.json').read_text());spec=statement['spec'];proof=json.loads((out/'proof.json').read_text());roots=[bytes.fromhex(x) for x in statement['roots']]
    for key in ('air','public','log_rows'):assert canonical[key]==spec[key]
    assert spec['public']==public_tape(message)
    rows=[json.loads((src/f'source-{i:02d}-rows.json').read_text())['rows'] for i in range(2)];count=(len(message)+16)//128+1;tables=spec['air']['tables']
    samples=sorted(set([0,1,len(rows[0])-1]+[80*b+k for b in range(count) for k in (0,1,78,79)]+[80*count]))
    checks=0
    for ti,indices in [(0,samples),(1,range(len(rows[1])))]:
        for r in indices:
            if r>=len(rows[ti]):continue
            for e in tables[ti]['constraints']:
                assert ref.evaluate(e,rows[ti],r,spec['public'])==0,(ti,r,e);checks+=1
    def natural_balance(traces):
        balance=collections.Counter();sent=collections.Counter();recv=collections.Counter()
        for ti,(table,trace) in enumerate(zip(tables,traces)):
            for r in range(len(trace)):
                for interaction in table['interactions']:
                    bits=[ref.evaluate(e,trace,r,spec['public']) for e in interaction['mult']];assert all(b in (0,1) for b in bits)
                    mult=sum(1<<i for i,b in enumerate(bits) if b)
                    if not mult:continue
                    msg=tuple(ref.evaluate(e,trace,r,spec['public']) for e in interaction['msg']);key=(interaction['bus'],msg)
                    balance[key]+=mult*(1 if interaction['send'] else -1);(sent if interaction['send'] else recv)[interaction['bus']]+=mult
        for b,send,msg in ref.public_messages(spec['air'],spec['public']):balance[(b,tuple(msg))]+=1 if send else -1;(sent if send else recv)[b]+=1
        return {k:v for k,v in balance.items() if v},dict(sent),dict(recv)
    balance,sent,recv=natural_balance(rows);assert not balance;assert sent==recv=={0:count,1:count,2:count-1,3:1,4:count,5:1}
    negatives=[]
    # Each change targets a concrete phase/reset/key/tag invariant.
    for name,r,c,value,checkrow in [('first-inactive',0,5232,0,0),('wrong-round-key',3,4116,(rows[0][3][4116]+1)%ref.P,3),('bad-phase-reset',80,5152,0,79),('wrong-tag-increment',80,5233,2,79),('early-stop',79,5232,0,78),('premature-block-stop',80,5232,0,79),('restart-padding',80*count+1,5232,1,80*count),('round-state-link',79,2544,1-rows[0][79][2544],78)]:
        bad=[row[:] for row in rows[0]];bad[r][c]=value
        assert any(ref.evaluate(e,bad,checkrow,spec['public']) for e in tables[0]['constraints']),name;negatives.append(name)
    bad=copy.deepcopy(rows);bad[1][0][-4:]=metadata(1,1,count);assert natural_balance(bad)[0];negatives.append('duplicate-endpoint-tag')
    assert bus.verify(proof,spec,roots)
    wire=codec.encode(proof,spec,roots);assert codec.decode(wire,spec,roots)==proof;(out/'proof.bin').write_bytes(wire)
    for index in [0,len(message),len(message)+52,len(message)+52+64*count,len(message)+56+64*count]:
        bad=copy.deepcopy(spec);bad['public'][index]^=1
        assert bad['public']!=public_tape(message)
        try:bus.verify(proof,bad,roots)
        except (ValueError,AssertionError,IndexError,KeyError):negatives.append('public-'+str(index))
        else:raise AssertionError('changed statement accepted')
    report={'status':'PASS','profile':'experimental-batched80-derived-public','tables':2,'blocks':count,'core_shape':[len(rows[0]),len(rows[0][0])],'endpoint_shape':[len(rows[1]),len(rows[1][0])],'boundary_rows':samples,'reference_residual_checks':checks,'natural_bus_sent':sent,'natural_bus_received':recv,'negative_tests':negatives,'proof_bytes_including_roots':len(wire),'additional_derived_public_bytes':4*(64*count+40),'proof_plus_additional_setup_bytes':len(wire)+4*(64*count+40),'endpoint_baseline_bytes':1289410,'binary_sha256':hashlib.sha256(wire).hexdigest(),'spec_sha256':hashlib.sha256((src/'spec.json').read_bytes()).hexdigest(),'scope':'Diagnostic Q8 proof; native all-row zerocheck and independent PCS verifier; full Lean batched phase/refinement and cryptographic soundness are not claimed.'}
    (out/'batched-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
