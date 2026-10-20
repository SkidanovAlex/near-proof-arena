"""Full canonical Expr/natural-count checks and fresh witness forgeries (not PCS tests)."""
import argparse,collections,copy,json,sys,time
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);a=p.parse_args();sys.path.append(str(Path(a.reference_dir).parent/'generic-air'));import reference as ref
    src=Path(a.fixture_directory);spec=json.loads((src/'spec.json').read_text());air=spec['air'];pub=spec['public'];ref.schema(air)
    traces=[json.loads((src/f'source-{t:02d}-rows.json').read_text())['rows'] for t in range(6)]
    def local(t,trace,onlyrows=None):
        count=0
        for r in (range(len(trace)) if onlyrows is None else onlyrows):
            for ei,e in enumerate(air['tables'][t]['constraints']):
                if ref.evaluate(e,trace,r,pub):return False,(t,r,ei)
                count+=1
        return True,count
    def traffic(rows):
        tally=collections.Counter();sent=collections.Counter();recv=collections.Counter()
        for table,tr in zip(air['tables'],rows):
            for r in range(len(tr)):
                for it in table['interactions']:
                    bits=[ref.evaluate(e,tr,r,pub) for e in it['mult']]
                    if any(v not in(0,1) for v in bits):return False,{},{}
                    mult=sum((1<<j)*v for j,v in enumerate(bits))
                    if mult:
                        message=tuple(ref.evaluate(e,tr,r,pub) for e in it['msg']);tally[(it['bus'],message)]+=mult*(1 if it['send'] else -1);(sent if it['send'] else recv)[it['bus']]+=mult
        return not any(tally.values()),dict(sent),dict(recv)
    start=time.perf_counter();residuals=0
    for t,tr in enumerate(traces):
        ok,count=local(t,tr);assert ok,count;residuals+=count;print('local PASS',t,count,flush=True)
    ok,sent,recv=traffic(traces);assert ok and sent==recv=={0:10,1:5,2:5,3:5,4:6,5:6}
    # Direct padded-block records independently reconstructed from byte strings.
    for c in range(2):
        msg=(src/f'message-{c}.bin').read_bytes();pad=msg+b'\x80'+bytes((111-len(msg))%128)+(8*len(msg)).to_bytes(16,'big')
        for b,it in enumerate(air['tables'][4+c]['interactions']):
            expected=[c,b]+[int.from_bytes(pad[128*b+8*w+6-2*l:128*b+8*w+8-2*l],'big') for w in range(16) for l in range(4)]
            assert [ref.evaluate(e,traces[4+c],0,pub) for e in it['msg']]==expected
    tests=[]
    def mutation(name,t,r,col,value,expect_local=None):
        rows=list(traces);rows[t]=list(rows[t]);rows[t][r]=rows[t][r].copy();rows[t][r][col]=value
        loc,_=local(t,rows[t],sorted({r,(r-1)%len(rows[t])}));bal,_,_=traffic(rows)
        assert not(loc and bal),name
        if expect_local is not None:assert loc==expect_local,(name,loc)
        tests.append(dict(name=name,local_accepts=loc,natural_balance_accepts=bal))
    mutation('fanout-two-to-three',2,0,2,1,True) # 2 -> 3, remains bit-valid
    mutation('fanout-two-to-zero',2,0,3,0,True)
    mutation('hidden-C-word6-record',2,0,124,traces[2][0][124]^1,True)
    mutation('hidden-A-word7-record',2,1,32,traces[2][1][32]^1,True)
    mutation('same-block-wrong-node',3,1,1,3,True)
    mutation('call-ID-splice',3,1,0,1,False)
    mutation('within-segment-tag-change',0,30,5233,1,False)
    mutation('wrong-core-reset-tag',0,80,5233,0,False)
    mutation('duplicate-record-ID',2,1,0,0,False)
    mutation('early-call-stop',3,5,2,0,False)
    mutation('padding-traffic',2,7,2,1,False)
    mutation('nonboolean-fanout',2,0,3,2,False)
    mutation('phase-reorder',3,1,4,0,False)
    mutation('endpoint-D-not-C',2,0,132,traces[2][0][132]^1,True)
    # Coherent swap of node's complete record in call1 step1: valid certified record,
    # but cannot splice its predecessor/full-state chain or its exact padded block.
    rows=list(traces);rows[3]=[r.copy() for r in traces[3]];rows[3][4][1]=1;rows[3][4][6:]=traces[2][1][4:]
    loc,_=local(3,rows[3]);bal,_,_=traffic(rows);assert not loc and not bal
    tests.append(dict(name='coherent-record-spliced-chain',local_accepts=loc,natural_balance_accepts=bal))
    report=dict(status='PASS',all_source_constraint_residuals=residuals,exact_padded_records=6,natural_sent=sent,natural_received=recv,forgeries=tests,seconds=time.perf_counter()-start,scope='Actual canonical AST full-witness checks with exact natural multiplicities, not cryptographic soundness or formal refinement.')
    (src/'record-checks.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
