#!/usr/bin/env python3
import argparse,hashlib,json,subprocess,sys
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',type=Path,required=True)
    p.add_argument('--lean-directory',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True)
    p.add_argument('--output-directory',type=Path,required=True);p.add_argument('--temporary-olean-dir',type=Path);a=p.parse_args()
    sys.path.insert(0,str(a.reference_dir));import pq384_primitives as primitive
    def frame(tag,parts):
        return primitive.PREFIX+len(tag).to_bytes(4,'little')+tag+len(parts).to_bytes(4,'little')+b''.join(len(x).to_bytes(8,'little')+x for x in parts)
    transcript=primitive.Transcript(b'bounded commit routing parity')
    rows=[];expected=[];history=[]
    for label,payload in [(b'',b''),(b'phase/commit',bytes(range(32))),(b'phase/commit',bytes(range(31,-1,-1)))]:
        prior=transcript.seed;message=frame(b'transcript/commit',[prior,label,payload])
        transcript.commit(label,payload)
        rows.append([list(prior),list(label),list(payload),list(message)])
        expected.append(transcript.seed);history.append({'prior':prior.hex(),'label':label.hex(),'payload':payload.hex(),'next':transcript.seed.hex()})
    base=rows[-1]
    bad=[]
    def mutation(name,s,l,p,m):bad.append(name);rows.append([list(s),list(l),list(p),list(m)])
    s,l,p,m=map(bytes,base)
    mutation('wrong prior seed',bytes([s[0]^1])+s[1:],l,p,m)
    mutation('stale prior seed',bytes.fromhex(history[0]['prior']),l,p,m)
    mutation('short seed',s[:-1],l,p,frame(b'transcript/commit',[s[:-1],l,p]))
    mutation('swapped label/payload',s,l,p,frame(b'transcript/commit',[s,p,l]))
    mutation('wrong domain',s,l,p,frame(b'transcript/init',[s,l,p]))
    mutation('extra operand',s,l,p,frame(b'transcript/commit',[s,l,p,b'']))
    mutation('missing operand',s,l,p,frame(b'transcript/commit',[s,l]))
    mutation('trailing byte',s,l,p,m+b'\0')
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True);inp=out/'inputs.json';result=out/'lean-results.json'
    inp.write_text(json.dumps([[s,[l,[p,m]]] for s,l,p,m in rows],separators=(',',':')))
    command=['lake','env']
    if a.temporary_olean_dir:
        leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=a.lean_directory,text=True).strip()
        command+=['env','LEAN_PATH='+str(a.temporary_olean_dir)+':'+leanpath]
    command+=['lean','--run',str(a.fixture),str(inp),str(result)]
    subprocess.run(command,cwd=a.lean_directory,check=True)
    got=json.loads(result.read_text());assert len(got)==len(rows)
    for actual,want in zip(got,expected):assert actual['operands'] and bytes(actual['next'])==want
    assert all(not r['operands'] and r['next']==[] for r in got[len(expected):])
    report={'status':'PASS','sequential_commits':len(expected),'negative_cases':bad,'history':history,
      'files':[{'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in [a.fixture,Path(__file__),a.reference_dir/'pq384_primitives.py',inp,result]],
      'limits':['Bounded actual commit operations only; no draw/rejection-sampling transition theorem.',
      'Per-instance seed wires must be constrained in recursive AIR; chronological hash events alone do not identify transcript instances.',
      'No new proof or cryptographic binding claim.']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['status','sequential_commits','negative_cases']}))

if __name__=='__main__':main()
