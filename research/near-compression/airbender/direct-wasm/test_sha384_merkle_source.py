#!/usr/bin/env python3
import argparse,hashlib,json,subprocess,sys
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',type=Path,required=True)
    p.add_argument('--lean-directory',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True)
    p.add_argument('--temporary-olean-dir',type=Path);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    sys.path.insert(0,str(a.reference_dir));import pq384_primitives as primitive
    cases=[];expected=[];negatives=0
    for depth in range(1,5):
        context=b'source tree/'+bytes([depth]);leaves=[hashlib.sha256(bytes([depth,i])).digest()[:i] for i in range(2**depth)]
        root,layers=primitive.merkle_tree(leaves,context);paths=[primitive.merkle_path(layers,i) for i in range(len(leaves))]
        assert all(primitive.verify_path(root,context,len(leaves),i,leaves[i],paths[i]) for i in range(len(leaves)))
        for i,leaf in enumerate(leaves):
            try:primitive.verify_path(root,context,len(leaves),i,leaf+b'\0',paths[i])
            except ValueError:negatives+=1
            else:raise AssertionError('changed source leaf accepted')
        cases.append({'depth':depth,'context':list(context),'leaves':[list(x) for x in leaves]})
        expected.append({'root':list(root),'layers':[[list(x) for x in layer] for layer in layers],
                         'paths':[[list(x) for x in path] for path in paths],'accepted':[True]*len(leaves),'changedAccepted':[False]*len(leaves)})
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True);inp=out/'inputs.json';result=out/'lean-results.json'
    inp.write_text(json.dumps(cases,separators=(',',':')))
    command=['lake','env']
    if a.temporary_olean_dir:
        leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=a.lean_directory,text=True).strip()
        command+=['env','LEAN_PATH='+str(a.temporary_olean_dir)+':'+leanpath]
    command+=['lean','--run',str(a.fixture),str(inp),str(result)]
    subprocess.run(command,cwd=a.lean_directory,check=True)
    assert json.loads(result.read_text())==expected
    report={'status':'PASS','depths':[1,2,3,4],'leaf_openings':30,'all_layer_digests':56,'changed_source_leaf_negatives':negatives,'lean_changed_source_leaf_negatives':30,
       'files':[{'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in [a.fixture,Path(__file__),a.reference_dir/'pq384_primitives.py',inp,result]],
       'limits':['Exact constructed fixed-source tree/path correspondence; no extraction from an unknown adversarial commitment.',
       'Formal differing-opening collision is supported on arbitrary and constructed path query sets; no collision-probability/QROM claim.']}
    assert report['all_layer_digests']==sum(sum(len(layer) for layer in x['layers']) for x in expected)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
