"""Multi-round integration, shape/transcript attacks, and fresh-oracle forgery."""
import copy,json,sys
from pathlib import Path
import pq384_batched_fold as f
from test_pq384_one_fold import native
from test_packed_claim_handoff import direct_mle
import struct


def forge(rows,args):
    # Recommit an altered first folded polynomial, preserving its residual,
    # then honestly rebuild every later round and all authentication paths.
    h,t,degree=f.public(args);n=len(rows);width=len(rows[0])
    matrices=[]
    for lane in range(len(h['batch_powers'])):
        cs=[rows[i][lane*args['packing']+j] if lane*args['packing']+j<width else 0
            for j in range(args['packing']) for i in range(n)]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:cs[i]=(cs[i]-cs[i^bit])%f.P
            bit*=2
        matrices.append([f.base(v) for v in cs])
    root,layers,leaves=f.source_tree(matrices,bytes.fromhex(h['context_hex']))
    cs=[f.ZERO]*degree
    for power,coefficients in zip(h['batch_powers'],matrices):
        cs=[f.add(a,f.mul(power,b)) for a,b in zip(cs,coefficients)]
    ws=f.weights(h['packed_point']);claim=h['batched_claim']
    assert root==args['expected_root'];rounds=[]
    while degree>64:
        q=[f.ZERO]*3
        for a,b,w,v in zip(cs[::2],cs[1::2],ws[::2],ws[1::2]):
            dc,dw=f.sub(b,a),f.sub(v,w)
            terms=[f.mul(a,w),f.add(f.mul(dc,w),f.mul(a,dw)),f.mul(dc,dw)]
            q=[f.add(x,y) for x,y in zip(q,terms)]
        wire=[list(v) for v in q];r,stage,claim=f.round_start(t,wire,claim)
        cs,ws=f.fold(cs,r),f.fold(ws,r)
        if not rounds:
            cs[0]=f.add(cs[0],ws[1]);cs[1]=f.sub(cs[1],ws[0])
        ctx,_=f.oracle_context(stage,degree//2);nr,nl,nv=f.tree(cs,ctx)
        sample=f.indices(t,nr,2*degree)
        queries=[{'source':f.opening(layers,leaves,i),'next':f.opening(nl,nv,i%degree)} for i in sample]
        rounds.append({'quadratic':wire,'next_root':nr.hex(),'queries':queries})
        f.absorb_queries(t,queries);root,layers,leaves,degree=nr,nl,nv,degree//2
    # Prove the forged final residual still passes its genuine terminal check.
    terminal={'profile':'near-pq384-terminal-v1','coefficients':[[list(v) for v in cs]]}
    f.verify_terminal(terminal,expected_root=root,stage_binding=stage,degree_bound=64,
                      domain_size=256,lanes=1,weights=[[list(v) for v in ws]],claim=claim)
    return {'profile':'near-pq384-batched-fold-v1','rounds':rounds,'terminal':terminal}


def run(binary,rows,packing):
    n,width=len(rows),len(rows[0]);c=native(binary,rows,packing,[0]);root=struct.pack('<12I',*c['root'])
    point=[(i+7,i+13,i+19,i+31) for i in range(n.bit_length()-1)]
    claims=[direct_mle([(r[j],0,0,0) for r in rows],point) for j in range(width)]
    args=dict(statement=b'multifold-fixture',parent_binding=b'AIR/current',expected_root=root,
              log_rows=n.bit_length()-1,width=width,packing=packing,row_point=point,column_claims=claims)
    proof=f.prove(rows,**args);assert f.verify(proof,**args);rejected=0
    def reject(p,a,reason=None):
        nonlocal rejected
        try:f.verify(p,**a)
        except ValueError as e:
            if reason is not None:assert str(e)==reason,(str(e),reason)
            rejected+=1
        else:raise AssertionError('invalid multiround proof accepted')
    for ri,rd in enumerate(proof['rounds']):
        for term in range(3):
            bad=copy.deepcopy(proof);bad['rounds'][ri]['quadratic'][term][0]=(bad['rounds'][ri]['quadratic'][term][0]+1)%f.P;reject(bad,args)
        for side in ('source','next'):
            for qi in (0,7):
                bad=copy.deepcopy(proof);q=bad['rounds'][ri]['queries'][qi][side];q['leaf'][0]=(q['leaf'][0]+1)%f.P;reject(bad,args)
                bad=copy.deepcopy(proof);bad['rounds'][ri]['queries'][qi][side]['path'][0]='00'*48;reject(bad,args)
        bad=copy.deepcopy(proof);bad['rounds'][ri]['queries'].pop();reject(bad,args)
        bad=copy.deepcopy(proof);bad['rounds'][ri]['next_root']='00'*48;reject(bad,args)
        bad=copy.deepcopy(proof);bad['rounds'][ri]['queries'][0]['source']['leaf'][0]=True;reject(bad,args)
    for altered in (proof['rounds'][:-1],proof['rounds']+proof['rounds'][-1:]):
        bad=copy.deepcopy(proof);bad['rounds']=altered;reject(bad,args)
    if len(proof['rounds'])>1:
        bad=copy.deepcopy(proof);bad['rounds'][0],bad['rounds'][1]=bad['rounds'][1],bad['rounds'][0];reject(bad,args)
        bad=copy.deepcopy(proof);bad['rounds'][1]=copy.deepcopy(bad['rounds'][0]);reject(bad,args)
    for pos in (0,63):
        bad=copy.deepcopy(proof);bad['terminal']['coefficients'][0][pos][0]=(bad['terminal']['coefficients'][0][pos][0]+1)%f.P;reject(bad,args)
    for key,value in [('parent_binding',b'wrong'),('statement',b'wrong'),('log_rows',12)]:
        bad=copy.deepcopy(args);bad[key]=value;reject(proof,bad)
    for col in (0,width//2,width-1):
        bad=copy.deepcopy(args);bad['column_claims']=[list(v) for v in claims]
        bad['column_claims'][col][3]=(bad['column_claims'][col][3]+1)%f.P;reject(proof,bad)
    for lane in range((width+packing-1)//packing):
        bad=copy.deepcopy(proof)
        leaf=bad['rounds'][0]['queries'][0]['source']['leaf']
        leaf[2*lane+1]=(leaf[2*lane+1]+1)%f.P;reject(bad,args)
    reject(forge(rows,args),args,'fold consistency')
    # Record that actual honest queries exercise both signs of the next pair.
    h,t,d=f.public(args);claim=h['batched_claim'];sides=[]
    for rd in proof['rounds']:
        _,_,claim=f.round_start(t,rd['quadratic'],claim)
        sample=f.indices(t,bytes.fromhex(rd['next_root']),2*d)
        sides.append(sorted(set(i//d for i in sample)))
        f.absorb_queries(t,rd['queries']);d//=2
    assert all(v==[0,1] for v in sides)
    return {'rows':n,'width':width,'packing':packing,'lanes':(width+packing-1)//packing,'rounds':len(proof['rounds']),
            'proof_json_bytes':len(json.dumps(proof,separators=(',',':')).encode()),
            'negative_checks':rejected,'query_sides_per_round':sides,
            'fresh_intermediate_and_all_later_rounds_rebuilt_attack_rejected':True},proof,args


def main():
    binary,source,dest=sys.argv[1:];dest=Path(dest);dest.mkdir(parents=True,exist_ok=True)
    # Independent direct polynomial evaluation checks the new Ext4 FFT.
    cs=[tuple((i+3)*(j+5)*991%f.P for j in range(4)) for i in range(8)]
    omega=pow(440564289,(1<<27)//32,f.P)
    encoded=f.fft(cs+[f.ZERO]*24,omega)
    for i,value in enumerate(encoded):
        x=pow(omega,i,f.P)
        assert value==tuple(sum(c[j]*pow(x,k,f.P) for k,c in enumerate(cs))%f.P for j in range(4))
    geometry=0
    for degree in (128,256,512,1024,2048):
        old=pow(440564289,(1<<27)//(4*degree),f.P)
        new=pow(440564289,(1<<27)//(2*degree),f.P)
        assert new==old*old%f.P
        for i in range(2*degree):
            assert pow(old,2*i,f.P)==pow(new,i%degree,f.P)*(1 if i//degree==0 else f.P-1)%f.P
            geometry+=1
    raw=json.loads(Path(source).read_text())['rows'];cases=[]
    for n,w,packing in [(64,17,2),(64,68,8),(8,544,32)]:
        result,proof,args=run(binary,[r[:w] for r in raw[:n]],packing);cases.append(result)
        (dest/f'proof-{n}x{w}.json').write_text(json.dumps(proof,indent=2)+'\n')
        (dest/f'statement-{n}x{w}.json').write_text(json.dumps({k:v.hex() if isinstance(v,bytes) else v for k,v in args.items()},indent=2)+'\n')
    result={'status':'PASS','cases':cases,'independent_fft_points':32,'independent_pair_indices':geometry,'scope':'BatchedlaneSHA384multiroundcoefficientfolding; witnessfreeverifier',
            'limits':['No proximity/RBR/QROM theorem','8queries/Ext4 not128-bitsecurity',
                      'No completeAIRintegration orrecursion','NoZK; terminalcoefficients disclosed']}
    (dest/'verified.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
