#!/usr/bin/env python3
import argparse,copy,hashlib,json,subprocess,sys
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',type=Path,required=True)
    p.add_argument('--lean-directory',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True)
    p.add_argument('--temporary-olean-dir',type=Path);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    sys.path.insert(0,str(a.reference_dir));import pq384_primitives as primitive
    cases=[];names=[]
    for count in [2,4,8]:
        leaves=[hashlib.sha256(bytes([i,count])).digest()[:i+1] for i in range(count)]
        context=b'bounded Merkle parity/'+bytes([count]);root,layers=primitive.merkle_tree(leaves,context)
        for i,leaf in enumerate(leaves):
            path=primitive.merkle_path(layers,i)
            cases.append(dict(root=list(root),context=list(context),count=count,index=i,leaf=list(leaf),path=[list(x) for x in path]))
            names.append('honest-'+str(count)+'-'+str(i))
    baseline=copy.deepcopy(cases[-1]);negative=[]
    def mutate(name,fn):
        x=copy.deepcopy(baseline);fn(x);cases.append(x);names.append(name);negative.append(name)
    mutate('root byte',lambda x:x['root'].__setitem__(0,x['root'][0]^1))
    mutate('context byte',lambda x:x['context'].__setitem__(0,x['context'][0]^1))
    mutate('leaf byte',lambda x:x['leaf'].__setitem__(0,x['leaf'][0]^1))
    mutate('wrong position',lambda x:x.__setitem__('index',x['index']^1))
    mutate('wrong count',lambda x:x.__setitem__('count',4))
    mutate('non power2',lambda x:x.__setitem__('count',7))
    mutate('count1',lambda x:x.__setitem__('count',1))
    mutate('out of range index',lambda x:x.__setitem__('index',8))
    mutate('short root',lambda x:x['root'].pop())
    mutate('short sibling',lambda x:x['path'][0].pop())
    mutate('omitted sibling',lambda x:x['path'].pop())
    mutate('extra sibling',lambda x:x['path'].append([0]*48))
    mutate('reordered siblings',lambda x:x['path'].reverse())
    for level in range(3):mutate('sibling byte '+str(level),lambda x,j=level:x['path'][j].__setitem__(0,x['path'][j][0]^1))
    expected=[];query_lists=[];original=primitive.hash_parts
    def frame(tag,parts):
        return primitive.PREFIX+len(tag).to_bytes(4,'little')+tag+len(parts).to_bytes(4,'little')+b''.join(len(x).to_bytes(8,'little')+x for x in parts)
    for c in cases:
        queries=[]
        def observe(tag,*parts):
            queries.append(list(frame(tag,parts)));return original(tag,*parts)
        primitive.hash_parts=observe
        try:accepted=primitive.verify_path(bytes(c['root']),bytes(c['context']),c['count'],c['index'],bytes(c['leaf']),[bytes(x) for x in c['path']])
        except ValueError:accepted=False
        finally:primitive.hash_parts=original
        expected.append(accepted);query_lists.append(queries)
    assert all(expected[:14]) and not any(expected[14:])
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True);inp=out/'inputs.json';result=out/'lean-results.json'
    inp.write_text(json.dumps(cases,separators=(',',':')))
    command=['lake','env']
    if a.temporary_olean_dir:
        leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=a.lean_directory,text=True).strip()
        command+=['env','LEAN_PATH='+str(a.temporary_olean_dir)+':'+leanpath]
    command+=['lean','--run',str(a.fixture),str(inp),str(result)]
    subprocess.run(command,cwd=a.lean_directory,check=True)
    got=json.loads(result.read_text())
    assert [x['accepted'] for x in got]==expected
    for i in range(14):assert got[i]['queries']==query_lists[i]
    for i,queries in enumerate(query_lists):
        if queries:assert got[i]['queries']==queries
    report={'status':'PASS','honest_paths':14,'exact_query_sequences':sum(bool(x) for x in query_lists),'negative_cases':negative,
       'files':[{'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in [a.fixture,Path(__file__),a.reference_dir/'pq384_primitives.py',inp,result]],
       'limits':['Byte-list semantic model excludes Python non-byte types; count/index/shape checks match typed accepted paths.',
       'Collision theorem locates distinct inputs in the two actual finite path-query supports; no SHA384 collision-resistance probability bound.',
       'No probability, QROM, or128-bit security bound inherited from existing64-byte widehash modules.']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
