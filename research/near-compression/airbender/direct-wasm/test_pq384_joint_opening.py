import argparse,copy,json,sys,tempfile,subprocess
from pathlib import Path
from contextlib import ExitStack

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--library',required=True);p.add_argument('--rs-binary',required=True)
    a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_joint_opening as joint
    from pq384_source_cache import SourceCache
    from pq384_native_fft import NativeFFT
    from packed_claim_handoff import mle_ext
    from pq384_one_fold import base
    work=Path(tempfile.mkdtemp(prefix='near-joint-small-'));args=[];paths=[]
    for j,n in enumerate([8,16]):
        width=3+j;rows=[[(i+1)*(c+3)+j for c in range(width)] for i in range(n)]
        inp=work/f'input{j}.json';cache=work/f'cache{j}';out=work/f'output{j}.json'
        inp.write_text(json.dumps(dict(rows=rows,packing=16,indices=[],cache_directory=str(cache))))
        subprocess.run([a.rs_binary,str(inp),str(out)],check=True,capture_output=True)
        m=json.loads((cache/'manifest.json').read_text());point=[(i+2+j,3+i,5,7) for i in range(n.bit_length()-1)]
        args.append(dict(statement=b'joint heterogeneous test',parent_binding=f'branch{j}'.encode(),expected_root=bytes.fromhex(m['root_hex']),
                         log_rows=n.bit_length()-1,width=width,packing=16,row_point=point,
                         column_claims=[mle_ext([base(row[c]) for row in rows],point) for c in range(width)]));paths.append(cache)
    with ExitStack() as stack:
        caches=[stack.enter_context(SourceCache(path,**{k:arg[k] for k in ('expected_root','log_rows','width','packing')})) for path,arg in zip(paths,args)]
        proof=joint.prove(caches,NativeFFT(a.library),args);assert joint.verify(proof,args)
        hs,ds,D,t,ps,ls,zs,claim=joint.public(args)
        # Independent coefficient reconstruction and sparse lift preserves evaluation.
        from pq384_terminal import horner
        from check_whir_handoff import add,mul
        lifted=[joint.branch_words(c,p,D) for c,p in zip(caches,ps)];checks=0
        for d,words in zip(ds,lifted):
            coefficients=[tuple(words[4*i:4*i+4]) for i in range(D)];original=coefficients[::D//d]
            omega=pow(440564289,(1<<27)//(4*D),joint.P)
            for s in range(4*D):
                x=pow(omega,s,joint.P)
                # Horner's variable is basefield, independently componentwise.
                def ev(cs,x):
                    result=[0]*4
                    for c in reversed(cs):result=[(v*x+b)%joint.P for v,b in zip(result,c)]
                    return tuple(result)
                assert ev(coefficients,x)==ev(original,pow(x,D//d,joint.P));checks+=1
    assert joint.eq_weights([joint.ONE,joint.ZERO])==[joint.ZERO,joint.ONE,joint.ZERO,joint.ZERO]
    rejected=0
    def reject(p,aa=args):
        nonlocal rejected
        try:joint.verify(p,aa)
        except (ValueError,IndexError,TypeError,KeyError):rejected+=1
        else:raise AssertionError('joint forgery accepted')
    for key in ['reduction','rounds']:
        bad=copy.deepcopy(proof)
        if key=='reduction':bad[key][0][0][0]^=1
        else:bad[key][0]['quadratic'][0][0]^=1
        reject(bad)
    for section in ['sources','folds']:
        bad=copy.deepcopy(proof);bad['queries'][0][section][0]['leaf'][0]^=1;reject(bad)
        bad=copy.deepcopy(proof);bad['queries'][0][section].pop();reject(bad)
    bad=copy.deepcopy(proof);bad['terminal']['coefficients'][0][0][0]^=1;reject(bad)
    aa=copy.deepcopy(args);aa[0]['row_point'][0]=(42,0,0,0);reject(proof,aa)
    aa=copy.deepcopy(args);aa[1]['parent_binding']=b'wrong';reject(proof,aa)
    aa=copy.deepcopy(args);aa.reverse();reject(proof,aa)
    print(json.dumps(dict(status='PASS',degrees=ds,independent_lift_checks=checks,negative_checks=rejected,
                         exceptional_eq_weights_pass=True,scope='honest algebra/negative tests only; no soundness theorem')))

if __name__=='__main__':main()
