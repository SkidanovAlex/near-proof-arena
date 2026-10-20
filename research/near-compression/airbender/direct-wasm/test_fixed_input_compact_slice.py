"""Fresh-process fixed-profile compact, request and complete-envelope checks."""
import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--reference-dir',required=True)
    ap.add_argument('--fixture',type=Path,required=True)
    ap.add_argument('--request',type=Path,required=True)
    ap.add_argument('--input-log',type=int,required=True)
    args=ap.parse_args();sys.path.insert(0,args.reference_dir)
    import pq384_compact_gkr_bus_codec as codec
    import prepared_gkr_envelope as envelope
    from verify_prepared_gkr_slice import verify
    folder=args.fixture;cap=args.input_log
    proof=json.loads((folder/'proof.json').read_text());statement=json.loads((folder/'statement.json').read_text())
    request=json.loads(args.request.read_text());spec=statement['spec'];roots=[bytes.fromhex(r) for r in statement['roots']]
    wire=codec.encode(proof,spec,roots,input_log=cap)
    assert codec.decode(wire,spec,roots,input_log=cap)==proof
    assert codec.encode(codec.decode(wire,spec,roots,input_log=cap),spec,roots,input_log=cap)==wire
    result=verify(wire,statement,request,input_log=cap)
    full=envelope.encode(wire,statement,request,input_log=cap)
    assert envelope.decode(full,input_log=cap)==(wire,statement,request)
    (folder/'proof.bin').write_bytes(wire);(folder/'envelope.bin').write_bytes(full)
    (folder/'request.json').write_bytes(args.request.read_bytes())
    env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),args.reference_dir])
    fresh=subprocess.run([sys.executable,str(Path(envelope.__file__)),str(folder/'envelope.bin'),
        str(folder/'request.json'),'--input-log',str(cap)],env=env,check=True,capture_output=True,text=True)
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,subprocess.CalledProcessError):rejected.append(name)
        else:raise AssertionError('accepted '+name)
    for other in (None,cap-1,cap+1):
        reject('compact changed cap '+str(other),lambda other=other:codec.decode(wire,spec,roots,input_log=other))
        reject('envelope changed cap '+str(other),lambda other=other:envelope.verify(full,request,input_log=other))
    for name,changed in [('truncated',full[:-1]),('trailing',full+b'x'),
                         ('wire cap',full[:len(envelope.MAGIC)]+bytes([cap+1])+full[len(envelope.MAGIC)+1:]),
                         ('proof byte',full[:-1]+bytes([full[-1]^1]))]:
        reject(name,lambda changed=changed:envelope.verify(changed,request,input_log=cap))
    for key,value in [('method','wrong'),('prepaid',request['prepaid']+1),('wasm_bytes',request['wasm_bytes']+[0])]:
        changed=copy.deepcopy(request);changed[key]=value
        reject('caller '+key,lambda changed=changed:envelope.verify(full,changed,input_log=cap))
    wrong=copy.deepcopy(statement);wrong['spec']['public'][39]=(wrong['spec']['public'][39]+1)%2013265921
    reject('published output',lambda:verify(wire,wrong,request,input_log=cap))
    report=dict(status='PASS',trusted_input_log=cap,proof_bytes=len(wire),complete_envelope_bytes=len(full),
                transport_overhead_bytes=len(full)-len(wire),envelope_plus_external_request_json_bytes=len(full)+(folder/'request.json').stat().st_size,
                exact_roundtrip=True,fresh_verifier=json.loads(fresh.stdout),rejections=rejected,
                limits=['Q8/Ext4 diagnostic; no quantum security or secure sub300000-byte claim.',
                        'Envelope carries cap byte, but caller configuration must match it.',
                        'Expected request is externally pinned; full NEAR semantics remain open.'])
    (folder/'compact-slice-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
