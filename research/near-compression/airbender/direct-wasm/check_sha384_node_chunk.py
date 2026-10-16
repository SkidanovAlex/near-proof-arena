"""Independent canonical AST and exact natural-count checks; no PCS acceptance claim."""
import argparse,collections,copy,hashlib,json,subprocess,sys,time,tempfile
from pathlib import Path
from verify_sha384_node_chunk import canonical,contract,PROFILE

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--rs-binary',required=True);a=p.parse_args();sys.path.append(a.reference_dir);sys.path.append(str(Path(a.reference_dir).parent/'generic-air'))
    import reference as ref
    from run_pq384_global_bus import choose_packing
    from packed_claim_handoff import packing_context
    src=Path(a.fixture_directory);spec=json.loads((src/'spec.json').read_text());cfg=json.loads((src/'config.json').read_text());ref.schema(spec['air']);pub=spec['public'];air=spec['air'];base,n,bits,uses=[cfg[k] for k in ('base','count','fanout_bits','uses')];data=2+bits
    traces=[json.loads((src/f'source-{t:02d}-rows.json').read_text())['rows'] for t in range(4)]
    for t,rows in enumerate(traces):assert len(rows)==1<<spec['log_rows'][t] and all(len(r)==air['tables'][t]['width'] for r in rows)
    def local(t,rows,indices=None):
        count=0
        for r in(range(len(rows)) if indices is None else indices):
            for i,e in enumerate(air['tables'][t]['constraints']):
                if ref.evaluate(e,rows,r,pub):return False,(r,i)
                count+=1
        return True,count
    def traffic(rows,actualair=air):
        counts=collections.Counter();totals=[collections.Counter(),collections.Counter()]
        for table,tr in zip(actualair['tables'],rows):
            for r in range(len(tr)):
                for it in table['interactions']:
                    bs=[ref.evaluate(e,tr,r,pub) for e in it['mult']]
                    if any(b not in(0,1) for b in bs):return False,totals
                    mult=sum(b<<j for j,b in enumerate(bs))
                    if mult:
                        msg=tuple(ref.evaluate(e,tr,r,pub) for e in it['msg']);counts[it['bus'],msg]+=mult*(1 if it['send'] else -1);totals[int(not it['send'])][it['bus']]+=mult
        return not any(counts.values()),totals
    started=time.perf_counter();residuals=0
    for t,rows in enumerate(traces):
        ok,num=local(t,rows);assert ok,(t,num);residuals+=num;print('local PASS',t,num,flush=True)
    ok,totals=traffic(traces);assert ok and totals[0]==totals[1]=={0:2*n,1:n,2:n,3:n,4:len(uses)}
    def limbs(words):return [(w>>(16*l))&65535 for w in words for l in range(4)]
    def words(bs):return [int.from_bytes(bytes(bs)[8*w:8*w+8],'big') for w in range(16)]
    for i,node in enumerate(cfg['nodes']):
        initial,block,final=node[:8],node[8:136],node[136:]
        expected=limbs(initial)+limbs(words(block))+limbs(final)+list(b''.join(w.to_bytes(8,'big') for w in final)[:48]);assert traces[2][i][data:]==expected
        assert traces[2][i][:2]==[i,1] and sum(traces[2][i][2+j]<<j for j in range(bits))==uses.count(base+i)
    for i,node in enumerate(uses):assert traces[3][i]==[i,1,node]+traces[2][node-base][data:]
    tests=[]
    def mutation(name,t,r,c,v,wantlocal=None):
        rows=list(traces);rows[t]=list(rows[t]);rows[t][r]=rows[t][r].copy();rows[t][r][c]=v
        loc,_=local(t,rows[t],sorted({r,(r-1)%len(rows[t])}));bal,_=traffic(rows);assert not(loc and bal),name
        if wantlocal is not None:assert loc==wantlocal,(name,loc)
        tests.append(dict(name=name,local_accepts=loc,natural_balance_accepts=bal))
    mutation('wrong-global-use-node',3,0,2,base+1,True)
    mutation('hidden-input-word7',3,0,3+28,traces[3][0][31]^1,True)
    mutation('hidden-output-word7',3,0,3+96+28,traces[3][0][127]^1,True)
    mutation('same-node-wrong-block',3,0,3+32,traces[3][0][35]^1,True)
    mutation('digest-not-full-C',3,0,3+128,traces[3][0][131]^1,True)
    mutation('fanout-high-bit-forgery',2,0,2+bits-1,1,True)
    mutation('fanout-nonboolean',2,0,2,2,False)
    mutation('record-padding-fanout',2,n,2,1,False)
    mutation('duplicate-local-nodeID',2,1,0,0,False)
    mutation('core-global-reset-bypass',0,80,5233,0,False)
    mutation('core-nodeID-midsegment',0,31,5233,1,False)
    mutation('use-omission',3,len(uses)-1,1,0,False)
    mutation('use-index-duplicate',3,1,0,0,False)
    wrongair=copy.deepcopy(air)
    for table in wrongair['tables'][:3]:
        for it in table['interactions']:
            assert it['msg'][0][0]=='+' and it['msg'][0][1]==['c',base]
            it['msg'][0][1][1]=base+1
    assert not traffic(traces,wrongair)[0];tests.append(dict(name='wrong-global-base',natural_balance_accepts=False))
    # Establish an externally fixed PCS root for the exact ordered uses BEFORE any proof.
    packing=choose_packing(spec['log_rows'][3],179);cache=Path(tempfile.mkdtemp(prefix='use-commit-',dir=src))/'cache';inp=src/'external-use-commit.json';result=src/'external-use-result.json'
    inp.write_bytes(canonical(dict(rows=traces[3],packing=packing,indices=[],cache_directory=str(cache))))
    subprocess.run([a.rs_binary,str(inp),str(result)],check=True,capture_output=True)
    root=json.loads((cache/'manifest.json').read_text())['root_hex']
    receipt=dict(profile=PROFILE,base=base,count=n,fanout_bits=bits,use_count=len(uses),air_sha384=hashlib.sha384(canonical(air)).hexdigest(),use_root=root,use_context_hex=packing_context(spec['log_rows'][3],179,packing).hex())
    receiptpath=src/'expected-use.json'
    if receiptpath.exists():assert json.loads(receiptpath.read_text())==receipt,'refuse to replace caller receipt'
    else:receiptpath.write_bytes(canonical(receipt))
    # Contract-only fixture: roots0..2 placeholders are NOT a claimed proof.
    st=dict(spec={**spec,'source_packings':[choose_packing(l,t['width']) for l,t in zip(spec['log_rows'],air['tables'])]},roots=['00'*48]*3+[root]);assert contract(st,receipt)
    # Fresh reordering preserves exact multiset balance/local constraints but must
    # not pass the original caller's ORDERED use commitment.
    reordered=list(traces);reordered[3]=[r.copy() for r in traces[3]]
    reordered[3][0][2:],reordered[3][1][2:]=reordered[3][1][2:],reordered[3][0][2:]
    assert local(3,reordered[3])[0] and traffic(reordered)[0]
    alternate_cache=Path(tempfile.mkdtemp(prefix='reordered-use-',dir=src))/'cache'
    alternate_input=alternate_cache.parent/'input.json';alternate_result=alternate_cache.parent/'result.json'
    alternate_input.write_bytes(canonical(dict(rows=reordered[3],packing=packing,indices=[],cache_directory=str(alternate_cache))))
    subprocess.run([a.rs_binary,str(alternate_input),str(alternate_result)],check=True,capture_output=True)
    alternate_root=json.loads((alternate_cache/'manifest.json').read_text())['root_hex'];assert alternate_root!=root
    alternate_st=copy.deepcopy(st);alternate_st['roots'][3]=alternate_root
    try:contract(alternate_st,receipt)
    except ValueError as error:assert str(error)=='mandatory external ordered-use root'
    else:raise AssertionError('fresh reordered use commitment')
    tests.append(dict(name='fresh-valid-reordered-use-commitment',local_accepts=True,natural_balance_accepts=True,original_expected_root_rejects=True,alternate_root=alternate_root))
    for name,edit in [('missing-receipt',lambda s,e:e.clear()),('wrong-root',lambda s,e:s['roots'].__setitem__(3,'01'*48)),('wrong-AIR-base',lambda s,e:s['spec'].__setitem__('air',wrongair)),('wrong-trusted-base',lambda s,e:e.__setitem__('base',base+1)),('wrong-context',lambda s,e:e.__setitem__('use_context_hex','00')),('proof-selected-use-count',lambda s,e:s['spec']['log_rows'].__setitem__(3,3))]:
        ss,ee=copy.deepcopy(st),copy.deepcopy(receipt);edit(ss,ee)
        try:contract(ss,ee)
        except (ValueError,AssertionError,KeyError):pass
        else:raise AssertionError(name)
        tests.append(dict(name=name,mandatory_contract_rejects=True))
    report=dict(status='PASS',source_shapes=[[len(r),len(r[0])] for r in traces],source_cells=sum(len(r)*len(r[0]) for r in traces),canonical_residuals=residuals,natural_sent=dict(totals[0]),natural_received=dict(totals[1]),full_state_records=n,ordered_use_records=len(uses),fanout_bits=bits,negative_cases=tests,external_use_root=root,external_use_receipt_bytes=receiptpath.stat().st_size,elapsed_seconds=time.perf_counter()-started,scope='Reference evaluator+exact natural balance+real external use PCS commitment. No full proof generated/verified by this test, no call-chain/padding provenance claim. Placeholder other roots used only to unit-test mandatory contract.')
    (src/'checks.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
