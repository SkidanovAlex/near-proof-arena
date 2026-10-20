"""Retained-proof transport regression; fresh verification without source rows."""
import copy,gzip,hashlib,json,subprocess,sys
from pathlib import Path
from unittest.mock import patch
import sha384_call_ext8_pcs as cp


def main():
    package=Path(__file__).resolve().parents[2]
    read=lambda p:json.loads(p.read_text())
    receipt=package/'results/ext8-node-batch/expected-use.json'
    calls_path=package/'results/ext8-linked-calls/calls.json'
    expected,calls=read(receipt),read(calls_path)
    reports=[]
    for q,saving in [(309,65832),(531,84000)]:
        source=package/f'results/call-ext8-q{q}'
        out=package/f'results/call-ext8-shared-q{q}';out.mkdir(exist_ok=True)
        proof=json.loads(gzip.decompress((source/'proof.json.gz').read_bytes()))
        statement=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()))
        old=(source/'proof.bin').read_bytes()
        assert cp.encode(proof,statement,expected,calls,queries=q)==old
        wire=cp.encode(proof,statement,expected,calls,queries=q,shared_sources=True)
        assert len(old)-len(wire)==saving
        for data in (old,wire):
            assert cp.canonical(cp.decode(data,statement,expected,calls,queries=q))==cp.canonical(proof)
        assert cp.encode(cp.decode(wire,statement,expected,calls,queries=q),statement,expected,calls,queries=q,shared_sources=True)==wire
        negatives=[]
        def reject(name,fn):
            try:fn()
            except ValueError:negatives.append(name)
            else:raise AssertionError(name)
        decode=lambda data:cp.decode(data,statement,expected,calls,queries=q)
        reject('truncated',lambda:decode(wire[:-1]))
        reject('trailing',lambda:decode(wire+b'\0'))
        offset=wire.index(cp.codec.SHARED_MAGIC)
        bad=bytearray(wire);bad[offset:offset+8]=cp.codec.MAGIC
        reject('shared-payload-old-version',lambda:decode(bytes(bad)))
        bad=bytearray(wire);bad[-1]^=1
        reject('authentication',lambda:decode(bytes(bad)))
        bad=bytearray(wire);bad[offset+8+240*len(proof['opening']['rounds'])+32]^=1
        reject('shared-source-leaf',lambda:decode(bytes(bad)))
        reject('query-budget',lambda:cp.decode(wire,statement,expected,calls,queries=q+1))
        # Fault injection isolates the decoder-to-verifier boundary. This is not
        # a forged authenticated proof: it tests that parsing cannot bypass PCS.
        corrupt=copy.deepcopy(proof['opening']);corrupt['queries']=[]
        with patch.object(cp.codec,'decode',return_value=corrupt):
            reject('decoded-opening-must-pass-full-pcs',lambda:decode(wire))
        layout,st,binding,_=cp.compile_layout(statement,expected,calls,queries=q)
        ob=cp.g.verify(layout,binding,proof['gkr']);bs=cp.branches(statement,ob)
        plan=cp.codec.stages(proof['opening'],st,cp.parent(binding,proof['gkr']),bs,ob['private_claim'],q)[0]
        assert cp.codec.source_key(plan[0])==cp.codec.source_key(plan[1])
        for key in ('root','context','half','width','indices'):
            altered=copy.deepcopy(plan[1])
            if key in ('root','context'):altered[key]=bytes([altered[key][0]^1])+altered[key][1:]
            elif key=='indices':altered[key][0]^=1
            else:altered[key]+=1
            assert cp.codec.source_key(plan[0])!=cp.codec.source_key(altered)
        bs[1]['row_point']=list(bs[1]['row_point']);bs[1]['row_point'][0]=cp.g.add(bs[1]['row_point'][0],cp.g.ONE)
        reject('distinct-branch-point-bound',lambda:cp.pcs.verify(proof['opening'],st,cp.parent(binding,proof['gkr']),bs,ob['private_claim'],queries=q))
        (out/'proof.bin').write_bytes(wire)
        temp=Path(f'/tmp/nearproof-shared-q{q}-statement.json');temp.write_text(json.dumps(statement))
        cmd=[sys.executable,str(Path(__file__).with_name('verify_sha384_call_ext8_bundle.py')),'--queries',str(q),'--call-proof',str(out/'proof.bin'),'--compression-proof',str(package/'results/ext8-node-batch/proof.bin'),'--statement',str(temp),'--receipt',str(receipt),'--calls',str(calls_path)]
        result=subprocess.run(cmd,capture_output=True,text=True);(out/'fresh-verifier.log').write_text(result.stdout+result.stderr);result.check_returncode()
        report=dict(status='PASS',queries=q,old_call_bytes=len(old),shared_call_bytes=len(wire),saved_bytes=saving,mixed_bundle_bytes=len(wire)+(package/'results/ext8-node-batch/proof.bin').stat().st_size+receipt.stat().st_size+calls_path.stat().st_size,negative_cases=negatives,geometry_key_separation_cases=5,canonical_roundtrip=True,fresh_verification=True,sha256=hashlib.sha256(wire).hexdigest(),scope='Ext8 call proof with shared source authentication; accompanying compression remains Q8/Ext4. Not PQ128, full recursion, or full NEAR.')
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');reports.append(report)
    print(json.dumps(reports,indent=2))

if __name__=='__main__':main()
