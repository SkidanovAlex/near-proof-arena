"""One-fold native-root integration and independently recommitted attack."""
import copy,json,struct,subprocess,sys,tempfile
from pathlib import Path
import pq384_one_fold as f
from test_packed_claim_handoff import direct_mle
from pq384_terminal import terminal_context,reconstructed_root,verify_terminal


def native(binary,rows,packing,indices):
    with tempfile.TemporaryDirectory(prefix='near-one-fold-') as d:
        src,dst=Path(d)/'in.json',Path(d)/'out.json'
        src.write_text(json.dumps({'rows':rows,'packing':packing,'indices':indices}))
        subprocess.run([binary,str(src),str(dst)],check=True,capture_output=True)
        return json.loads(dst.read_text())


def run(binary,rows,packing):
    n,width=len(rows),len(rows[0]);commit=native(binary,rows,packing,[0])
    root=struct.pack('<12I',*commit['root'])
    point=[(i+3,i+7,i+11,i+17) for i in range(n.bit_length()-1)]
    claims=[direct_mle([(r[c],0,0,0) for r in rows],point) for c in range(width)]
    args=dict(statement=b'one-fold-fixture',parent_binding=b'AIR/source/current',
              expected_root=root,log_rows=n.bit_length()-1,width=width,packing=packing,
              row_point=point,column_claims=claims)
    proof=f.prove(rows,**args);assert f.verify(proof,**args)
    rejected=0
    def reject(p,a,reason=None):
        nonlocal rejected
        try:f.verify(p,**a)
        except ValueError as e:
            if reason is not None:assert str(e)==reason,(str(e),reason)
            rejected+=1
        else:raise AssertionError('invalid fold accepted')
    for i in range(3):
        for j in range(4):
            bad=copy.deepcopy(proof);bad['round'][i][j]=(bad['round'][i][j]+1)%f.P;reject(bad,args)
    for i in (0,1,31,63):
        for j in range(4):
            bad=copy.deepcopy(proof);bad['terminal']['coefficients'][0][i][j]=(bad['terminal']['coefficients'][0][i][j]+1)%f.P;reject(bad,args)
    for i in range(8):
        bad=copy.deepcopy(proof);bad['queries'][i]['leaf'][0]=(bad['queries'][i]['leaf'][0]+1)%f.P;reject(bad,args)
        bad=copy.deepcopy(proof);bad['queries'][i]['path'][0]='00'*48;reject(bad,args)
    bad=copy.deepcopy(proof);bad['queries'].pop();reject(bad,args)
    bad=copy.deepcopy(proof);bad['next_root']='00'*48;reject(bad,args)
    for col in range(width):
        bad=copy.deepcopy(args);bad['column_claims']=[list(v) for v in claims]
        bad['column_claims'][col][0]=(bad['column_claims'][col][0]+1)%f.P;reject(proof,bad)
    for key in ('statement','parent_binding'):
        bad=copy.deepcopy(args);bad[key]+=b'other';reject(proof,bad)
    # New valid terminal commitment preserves the exact weighted residual,
    # but disagrees with the source fold. Supply authentic source paths at
    # the NEW transcript query indices: rejection must be folding consistency.
    h,t=f.public(args);r,stage,ws,claim=f.round_state(h,t,proof['round'])
    bad=copy.deepcopy(proof);cs=bad['terminal']['coefficients'][0]
    cs[0]=list(f.add(tuple(cs[0]),ws[1]));cs[1]=list(f.sub(tuple(cs[1]),ws[0]))
    context,omega=terminal_context(stage,64,256,1)
    newroot=reconstructed_root([[tuple(v) for v in cs]],context,256,omega)
    verify_terminal(bad['terminal'],expected_root=newroot,stage_binding=stage,
                    degree_bound=64,domain_size=256,lanes=1,weights=[[list(v) for v in ws]],claim=claim)
    indices=f.query_indices(t,newroot);opened=native(binary,rows,packing,indices)
    assert struct.pack('<12I',*opened['root'])==root
    bad['next_root']=newroot.hex()
    bad['queries']=[{'leaf':q['leaf'],'path':[struct.pack('<12I',*p).hex() for p in q['path']]}
                    for q in opened['openings']]
    reject(bad,args,'fold query consistency')
    return {'rows':n,'width':width,'packing':packing,'root_hex':root.hex(),
            'proof_json_bytes':len(json.dumps(proof,separators=(',',':')).encode()),
            'negative_checks':rejected,'fresh_terminal_preserving_residual_rejected':True},proof,args


def main():
    binary,source,out=sys.argv[1:];out=Path(out);out.mkdir(parents=True,exist_ok=True)
    raw=json.loads(Path(source).read_text())['rows'];cases=[]
    for n,w in [(64,2),(16,8)]:
        result,proof,args=run(binary,[r[:w] for r in raw[:n]],w);cases.append(result)
        (out/f'proof-{n}x{w}.json').write_text(json.dumps(proof,indent=2)+'\n')
        args={k:(v.hex() if isinstance(v,bytes) else v) for k,v in args.items()}
        (out/f'statement-{n}x{w}.json').write_text(json.dumps(args,indent=2)+'\n')
    report={'status':'PASS','cases':cases,'scope':'OnefoldD128toD64 withSHA384nativepackedroot, quadratic sumcheck,8authenticatedqueries, exactterminal',
            'limits':['No proximity/RBR/QROMsecurity theorem','DiagnosticExt4 and8queries not128-bit security',
                      'Singlelane fixedsize only; not fullAIRproof integration','No zero knowledge; terminalcoefficients disclosed']}
    (out/'verified.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
