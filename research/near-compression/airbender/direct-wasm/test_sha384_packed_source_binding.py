#!/usr/bin/env python3
import argparse,hashlib,json,struct,subprocess,sys
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',type=Path,required=True)
    p.add_argument('--lean-directory',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True)
    p.add_argument('--temporary-olean-dir',type=Path);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    sys.path.insert(0,str(a.reference_dir))
    from pq384_batched_fold import source_tree,opening,check_opening
    from packed_claim_handoff import packing_context
    from pq384_primitives import P,field_words
    degree=128;lanes=3;ctx=packing_context(3,35,16)
    matrices=[[(int((i+1)*(j+3)%P),0,0,0) for i in range(degree)] for j in range(lanes)]
    root,layers,leaves=source_tree(matrices,ctx)
    source=[list(struct.unpack('<6I',leaf)) for leaf in leaves]
    beta=[(1,2,3,4),(P-1,7,0,91),(0,0,9,5)]
    samples=[0,127,255,256,383,511]
    expected=[]
    for s in samples:
        index=s%(2*degree);op=opening(layers,leaves,index)
        pair=check_opening(op,root,ctx,2*degree,index,True,beta)
        projected=(pair[(s%(4*degree))//(2*degree)],)*2
        expected.append({'index':index,'pairs':[[[v0,v1] for v0,v1 in zip(*pair)],[[v0,v1] for v0,v1 in zip(*projected)]],'accepted':True})
    negatives=[];op=opening(layers,leaves,0)
    def reject(name,q,r=root,c=ctx,weights=beta):
        try:check_opening(q,r,c,2*degree,0,True,weights)
        except ValueError:negatives.append(name)
        else:raise AssertionError(name)
    for j in range(6):
        wrong={'leaf':list(op['leaf']),'path':op['path']};wrong['leaf'][j]=(wrong['leaf'][j]+1)%P;reject('lane slot '+str(j),wrong)
    reject('noncanonical field',{'leaf':[P]+op['leaf'][1:],'path':op['path']})
    reject('missing lane',{'leaf':op['leaf'][:-2],'path':op['path']})
    reject('extra lane',{'leaf':op['leaf']+[0,0],'path':op['path']})
    reject('wrong packing context',op,c=packing_context(3,36,16))
    reject('wrong root',op,r=bytes([root[0]^1])+root[1:])
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True);inp=out/'inputs.json';result=out/'lean-results.json'
    inp.write_text(json.dumps(dict(source=source,context=list(ctx),beta=[list(x) for x in beta],samples=samples,depth=8,degree=degree),separators=(',',':')))
    command=['lake','env']
    if a.temporary_olean_dir:
        leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=a.lean_directory,text=True).strip();command+=['env','LEAN_PATH='+str(a.temporary_olean_dir)+':'+leanpath]
    command+=['lean','--run',str(a.fixture),str(inp),str(result)]
    subprocess.run(command,cwd=a.lean_directory,check=True)
    got=json.loads(result.read_text());assert bytes(got['root'])==root
    assert [bytes(x) for x in got['source_bytes']]==leaves==[field_words(x) for x in source]
    assert got['samples']==expected
    assert got['changedAccepted']==[False]*(2*lanes)
    report={'status':'PASS','degree':degree,'lanes':lanes,'source_leaves':len(leaves),'samples':samples,
      'nonbase_Ext4_beta_coordinates':True,'negative_cases':negatives,'lean_changed_lane_negatives':2*lanes,
      'files':[{'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in [a.fixture,Path(__file__),a.reference_dir/'pq384_batched_fold.py',a.reference_dir/'packed_claim_handoff.py',a.reference_dir/'pq384_primitives.py',inp,result]],
      'limits':['Fixed arbitrary canonical base polynomial coefficients exercise actual source_tree FFT and check_opening; no AIR witness or adversarial representative extraction claimed.',
      'All4 Ext4 coordinates match via base-scalar weighting; source+aux branch scheduling and adaptive representative security remain separate.',
      'Finite-query collision reduction gives byte/word binding, not hash collision probability.']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
