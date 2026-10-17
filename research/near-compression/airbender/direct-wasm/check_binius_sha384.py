"""Pinned Binius64 SHA384 component probe; not a recursive/PQ128 benchmark."""
import gzip,hashlib,json,os,re,struct,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/binius-sha384'
REPO=Path('/tmp/nearproof-binius64')
PIN='4428e759dd27956bd5b9ae5025d67eb8ccc1accf'


def main():
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==PIN
    OUT.mkdir(exist_ok=True)
    graph=json.loads(gzip.decompress((OUT.parent/'gkr-hash-graph/graph.json.gz').read_bytes()))
    node=graph['nodes'][2];parts=[]
    for kind,value in node['parts']:
        parts.append(bytes.fromhex(value if kind=='literal' else graph['inputs'][value] if kind=='input' else graph['nodes'][value]['digest']))
    tag=node['tag'].encode();message=b'NEAR-PQ384-PRIMITIVES-V1'+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(struct.pack('<Q',len(p))+p for p in parts)
    assert len(message)==187 and hashlib.sha384(message).hexdigest()==node['digest']
    (OUT/'message.bin').write_bytes(message)
    exe=str(REPO/'target/release/binius-examples');env=os.environ.copy();env['RAYON_NUM_THREADS']='4'
    env.pop('NEARPROOF_BAD_SHA384_DIGEST',None);env.pop('NEARPROOF_SHA384_MESSAGE',None)
    results=[]
    def run(label,args,message_path=None,bad=False,expected=0):
        e=env.copy()
        if message_path:e['NEARPROOF_SHA384_MESSAGE']=str(message_path)
        if bad:e['NEARPROOF_BAD_SHA384_DIGEST']='1'
        r=subprocess.run([exe,*args],cwd=REPO,env=e,capture_output=True,text=True)
        log=r.stdout+r.stderr;(OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(),mtime=0))
        assert r.returncode==expected,(label,r.returncode,log[-1000:])
        expected_errors={'bad-digest':'circuit not satisfied','bad-message':'invalid assertion: value is not zero','bad-proof':'Merkle tree error'}
        if label in expected_errors:assert expected_errors[label] in log
        results.append(dict(label=label,exit_code=r.returncode))
        return re.sub(r'\x1b\[[0-9;]*m','',log)
    proof=OUT/'proof.bin'
    log=run('prove',['nearproof_sha384','prove','--message-len','187','--output',str(proof)],OUT/'message.bin')
    payload=int(re.search(r'proof_size_bytes[^0-9]+([0-9]+)',log).group(1))
    run('fresh',['nearproof_sha384','verify',str(proof),'--message-len','187'],OUT/'message.bin')
    run('bad-digest',['nearproof_sha384','verify',str(proof),'--message-len','187'],OUT/'message.bin',True,1)
    altered=bytes([message[0]^1])+message[1:];(OUT/'altered-message.bin').write_bytes(altered)
    run('bad-message',['nearproof_sha384','verify',str(proof),'--message-len','187'],OUT/'altered-message.bin',expected=1)
    data=bytearray(proof.read_bytes());data[len(data)//2]^=1;(OUT/'altered-proof.bin').write_bytes(data)
    run('bad-proof',['nearproof_sha384','verify',str(OUT/'altered-proof.bin'),'--message-len','187'],OUT/'message.bin',expected=1)
    for n in [0,111,112,127,128]:
        path=OUT/f'padding-{n}.bin';path.write_bytes(bytes((i*17)%256 for i in range(n)))
        run(f'padding-{n}',['nearproof_sha384','prove','--message-len',str(n)],path)
    run('sha512-regression',['sha512','prove','--message-len','187'])
    stats=run('statistics',['nearproof_sha384','stat','--message-len','187'])
    assert 'Private Section: 2,276' in stats and 'Inout: 30' in stats
    assert 'AND constraints: 1,831' in stats and 'ZERO constraints: 451' in stats
    (OUT/'statistics.txt').write_text(stats)
    report=dict(upstream_commit=PIN,status='SHA384_COMPONENT_PROVED_AND_VERIFIED',message_bytes=len(message),
        compression_blocks=2,message_sha384=hashlib.sha384(message).hexdigest(),proof_payload_bytes=payload,
        serialized_proof_bytes=proof.stat().st_size,public_inout_words=30,public_inout_bytes=240,
        committed_word_count=2276,bitand_constraints=1831,zero_constraints=451,results=results,
        rejection_stages={'bad-digest':'witness circuit assertion before proof verification','bad-message':'proof verifier','bad-proof':'proof verifier Merkle authentication'},
        security_scope='Pinned verifier SECURITY_BITS=96 controls FRI query phase only; default SHA256 Merkle hash suite. Not a full/PQ128 security certificate.',
        limitations=['Single public-message SHA384 relation, not transcript routing or recursive bundle verification.',
                     '64-bit word counts are not comparable units to BabyBear AIR cells.',
                     'No matched performance benchmark, Lean compiler proof, full NEAR or secure-size claim.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':main()
