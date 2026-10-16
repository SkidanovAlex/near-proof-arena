"""Exact byte/padding routing and fresh-proof commitment/truncation negatives."""
import argparse,collections,copy,json,os,subprocess,sys
from pathlib import Path
from verify_sha384_committed_gkr import verify

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--proof-directory',required=True);p.add_argument('--rs-binary',required=True);p.add_argument('--folded-library',required=True);p.add_argument('--fft-library',required=True);a=p.parse_args();sys.path.append(a.reference_dir);sys.path.append(str(Path(a.reference_dir).parent/'generic-air'))
    import reference as ref
    import pq384_gkr_bus as bus
    import pq384_compact_gkr_bus_codec as codec
    src=Path(a.fixture_directory);out=Path(a.proof_directory);canonical=json.loads((src/'spec.json').read_text());statement=json.loads((out/'statement.json').read_text());spec=statement['spec'];expected=json.loads((out/'expected-input.json').read_text());wire=(out/'proof.bin').read_bytes();tables=spec['air']['tables'];rows=[json.loads((src/f'source-{i:02d}-rows.json').read_text())['rows'] for i in range(4)]
    assert verify(wire,statement,expected)
    checks=0
    for ti in (2,3):
        for r in range(len(rows[ti])):
            for e in tables[ti]['constraints']:
                assert ref.evaluate(e,rows[ti],r,spec['public'])==0;checks+=1
    def balance(traces):
        values=collections.Counter();sent=collections.Counter();recv=collections.Counter()
        for table,trace in zip(tables,traces):
            for r in range(len(trace)):
                for interaction in table['interactions']:
                    bits=[ref.evaluate(e,trace,r,spec['public']) for e in interaction['mult']];assert all(b in(0,1) for b in bits)
                    mult=sum(1<<i for i,b in enumerate(bits) if b)
                    if mult:
                        msg=tuple(ref.evaluate(e,trace,r,spec['public']) for e in interaction['msg']);values[(interaction['bus'],msg)]+=mult*(1 if interaction['send'] else -1);(sent if interaction['send'] else recv)[interaction['bus']]+=mult
        for b,send,msg in ref.public_messages(spec['air'],spec['public']):values[(b,tuple(msg))]+=1 if send else -1;(sent if send else recv)[b]+=1
        return {k:v for k,v in values.items() if v},dict(sent),dict(recv)
    mismatch,sent,recv=balance(rows);assert not mismatch;assert sent==recv=={0:4,1:4,2:3,3:1,4:4,5:1,6:376}
    negatives=[]
    for ti,r,col,name in [(2,0,0,'framing-prefix'),(2,0,10,'nonboolean-input'),(3,2,8*120,'padding-delimiter'),(3,3,8*127,'bit-length-tail'),(3,1,1025,'padding-block-selector')]:
        bad=[row[:] for row in rows[ti]];bad[r][col]=2 if name=='nonboolean-input' else 1-bad[r][col]
        assert any(ref.evaluate(e,bad,r,spec['public']) for e in tables[ti]['constraints']),name;negatives.append(name)
    for name,alter in [('missing-root',lambda x:x.pop('input_root')),('wrong-root',lambda x:x.update(input_root='00'*48)),('wrong-length',lambda x:x.update(declared_length=375)),('wrong-context',lambda x:x.update(input_context_hex='00')),('wrong-air',lambda x:x.update(air_sha384='00'*48))]:
        bad=copy.deepcopy(expected);alter(bad)
        try:verify(wire,statement,bad)
        except (AssertionError,ValueError,IndexError,KeyError):negatives.append(name)
        else:raise AssertionError(name)
    for name,badwire in [('truncated-wire',wire[:-1]),('trailing-wire',wire+b'\0'),('changed-source-root',wire[:6]+bytes([wire[6]^1])+wire[7:]),('changed-opening',wire[:-1]+bytes([wire[-1]^1]))]:
        try:verify(badwire,statement,expected)
        except (AssertionError,ValueError,IndexError,KeyError):negatives.append(name)
        else:raise AssertionError(name)
    def fresh(name,changed,logs):
        fixture=out/(name+'-fixture');fixture.mkdir(exist_ok=True);cs=copy.deepcopy(canonical);cs['log_rows']=logs;(fixture/'spec.json').write_text(json.dumps(cs,separators=(',',':')))
        for ti,trace in enumerate(changed):(fixture/f'source-{ti:02d}-rows.json').write_text(json.dumps({'rows':trace},separators=(',',':')))
        dest=out/(name+'-proof');command=[sys.executable,str(Path(a.reference_dir)/'run_pq384_gkr_bus.py'),'--reference-dir',a.reference_dir,'--spec',str(fixture/'spec.json'),'--source-directory',str(fixture),'--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(dest)]
        result=subprocess.run(command,capture_output=True,text=True);(out/(name+'.log')).write_text(result.stdout+result.stderr)
        assert (dest/'proof.json').exists(),result.stderr
        st=json.loads((dest/'statement.json').read_text());pr=json.loads((dest/'proof.json').read_text());rt=[bytes.fromhex(r) for r in st['roots']]
        return result,st,pr,rt,dest
    # The unused second input row remains Boolean and generates no byte sends.
    # Fresh fullAIR proof accepts its new root, but the required caller root rejects.
    changed=copy.deepcopy(rows);changed[2][1][0]=1
    assert not balance(changed)[0]
    result,st,pr,rt,dest=fresh('different-input-root',changed,canonical['log_rows']);assert result.returncode==0 and bus.verify(pr,st['spec'],rt)
    freshwire=codec.encode(pr,st['spec'],rt);(dest/'proof.bin').write_bytes(freshwire)
    try:verify(freshwire,st,expected)
    except (AssertionError,ValueError):negatives.append('fresh-valid-proof-wrong-expected-root')
    else:raise AssertionError('external root optional')
    # Missing last two block rows is locally valid: exact natural routing must fail.
    truncated=rows[:3]+[rows[3][:2]];assert balance(truncated)[0]
    assert all(ref.evaluate(e,truncated[3],r,spec['public'])==0 for r in range(2) for e in tables[3]['constraints'])
    logs=canonical['log_rows'][:];logs[3]=1
    result,st,pr,rt,dest=fresh('truncated-padding',truncated,logs);assert result.returncode!=0;assert bus.verify_local(pr,st['spec'],rt)
    try:bus.verify(pr,st['spec'],rt)
    except (AssertionError,ValueError):negatives.append('fresh-locally-valid-truncated-padding')
    else:raise AssertionError('missing padding records accepted')
    report={'status':'PASS','reference_new_table_residual_checks':checks,'exact_natural_bus_sent':sent,'exact_natural_bus_received':recv,'negative_tests':negatives,'fresh_different_root_underlying_full_proof_accepts':True,'fresh_different_root_component_rejects':True,'fresh_truncated_padding_local_and_PCS_accept':True,'fresh_truncated_padding_global_reject':True,'scope':'Mandatory root boundary and actual byte routing tested; full new AIR semantic proof and recursive producer routing not claimed.'}
    (out/'committed-gkr-negatives.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
