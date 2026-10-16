#!/usr/bin/env python3
import argparse,copy,json,subprocess,sys,time,hashlib
from pathlib import Path
import pq384_ext8_pcs as p
import pq384_ext8_reference as e

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--verify-only',action='store_true');a=ap.parse_args()
    if a.verify_only:
        env=json.loads((a.output/'proof.json').read_text());assert p.verify(env['proof'],env['config'],bytes.fromhex(env['expected_root']));print('PASS fresh process');return
    a.output.mkdir(parents=True,exist_ok=True)
    d=32;coeff=[(i*i*9876543+i*12345+77)%e.P for i in range(d)]
    point=[[(i+1)*(j+2)*137%e.P for j in range(8)] for i in range(d.bit_length()-1)]
    claim=e.ZERO
    for c,w in zip(coeff,p.eqweights(point)):claim=e.add(claim,e.scale(w,c))
    config=dict(profile=p.PROFILE,degree=d,queries=314,point=point,claim=list(claim),statement=b'actual-Ext8-coefficient-MLE-reference/nonbase-point'.hex())
    root=p.source_tree(coeff,config)['root'];t=time.perf_counter();proof=p.prove(coeff,config,root);prove_time=time.perf_counter()-t
    calls=blocks=0;old=p.h.hash_parts
    def counted(tag,*parts):
        nonlocal calls,blocks
        n=len(p.h.PREFIX)+4+len(tag)+4+sum(8+len(x) for x in parts)
        calls+=1;blocks+=(n+17+127)//128
        return old(tag,*parts)
    p.h.hash_parts=counted;t=time.perf_counter();assert p.verify(proof,config,root);verify_time=time.perf_counter()-t;p.h.hash_parts=old
    negatives=[]
    def reject(name,edit):
        x,y,z=copy.deepcopy(proof),copy.deepcopy(config),root
        x,y,z=edit(x,y,z)
        try:p.verify(x,y,z)
        except (ValueError,TypeError,KeyError,IndexError):negatives.append(name)
        else:raise AssertionError('accepted '+name)
    def mutate(path,value):
        def edit(x,y,z):
            v=x
            for k in path[:-1]:v=v[k]
            v[path[-1]]=value;return x,y,z
        return edit
    reject('wrong root',lambda x,y,z:(x,y,bytes([z[0]^1])+z[1:]))
    for key,value in [('profile','wrong'),('queries',313),('degree',16),('statement',b'other'.hex()),('claim',[0]*8),('point',[[0]*8]*5)]:
        reject('config '+key,lambda x,y,z,k=key,v=value:(x,{**y,k:v},z))
    for i in range(5):
        reject('quadratic '+str(i),mutate(['rounds',i,'quadratic',0,0],(proof['rounds'][i]['quadratic'][0][0]+1)%e.P))
        reject('fold root '+str(i),mutate(['rounds',i,'root'],'00'*48))
    reject('profile',mutate(['profile'],'old-ext4-profile'))
    reject('terminal',mutate(['terminal',0],(proof['terminal'][0]+1)%e.P))
    reject('noncanonical ext',mutate(['terminal',0],e.P))
    reject('boolean ext',mutate(['terminal',0],True))
    reject('source leaf',mutate(['queries',0,0,0,'leaf'],'00'*8))
    reject('path',mutate(['queries',0,0,0,'path',0],'00'*48))
    reject('missing query',mutate(['queries'],proof['queries'][:-1]))
    reject('reordered query',mutate(['queries'],list(reversed(proof['queries']))))
    # A source change cannot generate a fresh accepted proof against the fixed root.
    bad=coeff[:];bad[0]=(bad[0]+1)%e.P
    try:p.prove(bad,config,root)
    except ValueError:negatives.append('fresh changed source fixed root')
    else:raise AssertionError('fresh source bypass')
    env=dict(proof=proof,config=config,expected_root=root.hex())
    data=json.dumps(env,separators=(',',':')).encode();(a.output/'proof.json').write_bytes(data)
    child=subprocess.run([sys.executable,__file__,'--output',str(a.output),'--verify-only'],check=True,capture_output=True,text=True)
    report=dict(status='PASS',profile=p.PROFILE,degree=d,queries=314,extension=8,source_encoding='2base-u32/leaf',fold_encoding='2x8u32/leaf',
      proof_json_bytes=len(json.dumps(proof,separators=(',',':')).encode()),whole_envelope_json_bytes=len(data),root_bytes=48,
      canonical_config_bytes=len(p.config_bytes(config)),verify_hash_calls=calls,verify_sha384_blocks=blocks,
      prove_seconds=prove_time,verify_seconds=verify_time,negative_count=len(negatives),negatives=negatives,fresh_process=child.stdout.strip(),
      limitation='Scalar coefficient-MLE source; not complete packed joint/AIR profile. Ideal replay bound only; root extraction, FS/QROM and upstream composition open.',
      files=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in [Path(__file__),Path(p.__file__),Path(e.__file__),a.output/'proof.json']])
    (a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
