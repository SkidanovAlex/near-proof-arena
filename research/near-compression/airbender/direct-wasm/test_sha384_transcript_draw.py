#!/usr/bin/env python3
"""Actual and scripted hash-source parity; no hash-uniformity assertion."""
import argparse,hashlib,json,struct,subprocess,sys
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',type=Path,required=True)
    p.add_argument('--lean-directory',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True)
    p.add_argument('--temporary-olean-dir',type=Path);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    sys.path.insert(0,str(a.reference_dir));import pq384_primitives as primitive
    original=primitive.hash_parts;P=primitive.P;limit=primitive.LIMIT
    seed=original(b'transcript/init',b'draw transition parity')
    allreject=struct.pack('<12I',*([limit]*12))
    scripted=struct.pack('<12I',limit,2**32-1,0,P-1,P,P+1,limit,limit,limit,limit,limit,limit)
    cases=[('actual-small',1,1,4,None),('actual-ext4',2,4,4,None),('actual-multiblock',4,4,8,None),
      ('forced-reject-stop',1,3,2,[scripted]),('forced-crossblock',13,1,3,[struct.pack('<12I',*range(12)),scripted]),
      ('exhaustion',1,1,2,[allreject,allreject]),('zero-count',0,4,2,None),('zero-coefficients',1,0,2,None),
      ('over-count',4097,1,2,None),('over-coefficients',1,65,2,None),('zero-budget',1,1,0,None),('over-budget',1,1,2**20+1,None)]
    rows=[];expected=[];logs=[]
    for name,count,coeff,budget,squeezes in cases:
        oracle=[];calls=[]
        def hooked(tag,*parts):
            if tag==b'transcript/squeeze' and squeezes is not None:
                counter=int.from_bytes(parts[2],'little');value=squeezes[counter]
            else:value=original(tag,*parts)
            oracle.append([[list(tag),[list(x) for x in parts]],list(value)])
            calls.append({'tag':tag.decode(),'parts_hex':[x.hex() for x in parts],'digest_hex':value.hex()})
            return value
        transcript=primitive.Transcript(b'unused');transcript.seed=seed
        primitive.hash_parts=hooked
        try:
            values,meta=transcript.draw(b'label',count,coeff,budget)
            want={'accepted':True,'seed':list(transcript.seed),'values':[v for row in values for v in row],
                  'blocks':meta['blocks'],'rejected':meta['rejected_words']}
        except ValueError:
            assert transcript.seed==seed
            want={'accepted':False,'seed':list(seed)}
        finally:primitive.hash_parts=original
        rows.append({'seed':list(seed),'label':list(b'label'),'count':count,'coefficients':coeff,'max_blocks':budget,
                     'actual_hash':squeezes is None,'oracle':oracle})
        expected.append(want);logs.append({'name':name,'calls':calls})
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True);inp=out/'inputs.json';result=out/'lean-results.json'
    inp.write_text(json.dumps(rows,separators=(',',':')))
    command=['lake','env']
    if a.temporary_olean_dir:
        leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=a.lean_directory,text=True).strip()
        command+=['env','LEAN_PATH='+str(a.temporary_olean_dir)+':'+leanpath]
    command+=['lean','--run',str(a.fixture),str(inp),str(result)]
    subprocess.run(command,cwd=a.lean_directory,check=True)
    got=json.loads(result.read_text());assert got==expected
    assert got[3]['rejected']==2 and got[3]['values']==[0,P-1,0] and got[3]['blocks']==1
    assert got[4]['rejected']==2 and got[4]['blocks']==2
    assert not got[5]['accepted']
    # Oracle-mode parity also checks exact hash input tuple dependencies: corrupt
    # the first request key so Lean cannot find the expected squeeze input.
    broken=json.loads(inp.read_text());broken[3]['oracle'][0][0][1][0][0]^=1
    brokenpath=out/'wrong-request-input.json';brokenpath.write_text(json.dumps([broken[3]]))
    negativepath=out/'wrong-request-result.json';command[-2:]=[str(brokenpath),str(negativepath)]
    subprocess.run(command,cwd=a.lean_directory,check=True)
    assert json.loads(negativepath.read_text())==[{'accepted':False,'seed':list(seed)}]
    (out/'python-hash-events.json').write_text(json.dumps(logs,indent=2)+'\n')
    report={'status':'PASS','cases':[c[0] for c in cases],'oracle_input_mutations_rejected':1,
      'files':[{'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in [a.fixture,Path(__file__),a.reference_dir/'pq384_primitives.py',inp,result]],
      'limits':['Values/ranges/order/counter/meta/seed parity only; SHA output uniformity or independence not assumed.',
                'Scripted squeeze blocks exercise rejection and exhaustion, not a cryptographic hash implementation.',
                'Flat coefficient vector matches Python row-major grouping; next recursive AIR enforcement remains open.']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
