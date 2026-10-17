"""Authenticate actual call PCS source leaves against the reconstructed fixed table."""
import argparse,copy,gzip,hashlib,json,struct,subprocess
from pathlib import Path
import sha384_call_pcs as cp
import pq384_primitives as primitive
from verify_sha384_linked_calls import reconstructed_use_leaves


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    source=package/'results/ext8-linked-calls';read=lambda f:json.loads(f.read_text())
    st=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()));rows=read(source/'rows.json');calls=read(source/'calls.json')
    receipt=read(package/'results/ext8-node-batch/expected-use.json')
    proof=json.loads(gzip.decompress((package/'results/ext8-call-pcs/proof.json.gz').read_bytes()))
    layout,statement,binding,_=cp.compile_layout(st,receipt,calls);ob=cp.g.verify(layout,binding,proof['gkr']);branches=cp.branches(st,ob)
    degrees,D,contexts,betas,roots,fold_contexts,challenges,samples=cp.pcs.replay(proof['opening'],statement,cp.parent(binding,proof['gkr']),branches,ob['private_claim'])
    leaves,context=reconstructed_use_leaves(rows,st['spec']['log_rows'][3],st['spec']['source_packings'][3])
    root,tree=primitive.merkle_tree(leaves,context);assert root.hex()==st['roots'][3]==receipt['use_root']
    cases=[];indices=[]
    for sample,query in zip(samples,proof['opening']['queries']):
        for opening,branch,d,ctx,weights in zip(query['sources'],branches,degrees,contexts,betas):
            index=sample%(2*d);indices.append(index)
            assert branch['root']==root.hex() and ctx==context and len(leaves)==2*d
            assert primitive.field_words(opening['leaf'])==leaves[index]
            words=list(struct.unpack('<'+'I'*(len(leaves[index])//4),leaves[index]))
            assert opening['leaf']==words and all(0<=x<primitive.P for x in words)
            got=cp.pcs.check_opening(opening,root,context,len(leaves),index,True,weights)
            expected=[]
            for side in range(2):
                value=cp.g.ZERO
                for lane,w in enumerate(weights):value=cp.g.add(value,cp.g.mul(w,cp.g.base(words[2*lane+side])))
                expected.append(value)
            assert tuple(expected)==got
            cases.append(dict(root=list(root),context=list(context),count=len(leaves),index=index,
                leaf=list(leaves[index]),path=[list(bytes.fromhex(x)) for x in opening['path']]))
    positives=len(cases);assert positives==16
    for mutation in ('leaf','root','context','sibling','index'):
        bad=copy.deepcopy(cases[0])
        if mutation=='sibling':bad['path'][0][0]^=1
        elif mutation=='index':bad['index']^=1
        else:bad[mutation][0]^=1
        cases.append(bad)
    path=out/'paths.json';path.write_text(json.dumps(cases,separators=(',',':')));output=out/'lean-output.json'
    run=subprocess.run(['lake','env','lean','--run','SHA384MerklePathFixture.lean',str(path),str(output)],cwd=package,text=True,capture_output=True,timeout=120)
    (out/'lean.log').write_text(run.stdout+run.stderr);run.check_returncode()
    assert [x['accepted'] for x in read(output)]==[True]*positives+[False]*5
    report=dict(status='PASS',source_leaves=len(leaves),authenticated_source_paths=positives,unique_indices=len(set(indices)),
        negative_paths=5,canonical_words_equal_fixed_source=True,weighted_antipodal_pairs_match=True,
        source_root=root.hex(),fixture_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in
          [Path(__file__),package/'NearCompression/CallMerkleOpening.lean',package/'SHA384MerklePathFixture.lean',package/'airbender/direct-wasm/verify_sha384_linked_calls.py']},
        scope='Actual source openings match a fixed tree reconstructed from diagnostic rows and pass Lean SHA384 path verification. Formal disagreement implies a hash collision; no collision probability or extraction of a low-degree representative from an adversarial root is proved. PCS proximity, adaptive soundness and QROM remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
