"""Dynamic recursion-work inventory for actual verifier paths, not gate estimates.

Counts reference hash_parts and Ext4 operation calls without replacing them.
SHA384 block counts include actual framing and standard128-byte block padding.
The profiler slows execution; timings here are not performance benchmarks.
"""
import argparse,json,sys,hashlib
from pathlib import Path
from collections import Counter,defaultdict
import pq384_primitives as primitives
import check_whir_handoff as field
import pq384_global_table_air as air
import pq384_global_table_codec as codec

def measure(fn):
    tags=defaultdict(lambda:dict(calls=0,framed_input_bytes=0,compression_blocks=0))
    arithmetic=Counter();codes={getattr(field,n).__code__:n for n in ('add','sub','mul')}
    def trace(frame,event,arg):
        if event!='call':return
        code=frame.f_code
        if code is primitives.hash_parts.__code__:
            tag=frame.f_locals['tag'];parts=frame.f_locals['parts']
            length=len(primitives.PREFIX)+4+len(tag)+4+sum(8+len(p) for p in parts)
            v=tags[tag.decode('ascii')];v['calls']+=1;v['framed_input_bytes']+=length
            v['compression_blocks']+=(length+17+127)//128
        elif code in codes:arithmetic[codes[code]]+=1
    sys.setprofile(trace)
    try:result=fn()
    finally:sys.setprofile(None)
    assert result
    return dict(hash_tags=dict(sorted(tags.items())),total_hash_calls=sum(x['calls'] for x in tags.values()),
                total_sha384_compression_blocks=sum(x['compression_blocks'] for x in tags.values()),
                ext4_operation_calls=dict(arithmetic))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('output',type=Path)
    mode=ap.add_mutually_exclusive_group()
    mode.add_argument('--bus',action='store_true');mode.add_argument('--joint',action='store_true')
    ap.add_argument('--binary',type=Path);a=ap.parse_args()
    statement=json.loads((a.directory/'statement.json').read_text());spec=statement['spec']
    wire=(a.binary or a.directory/'proof.bin').read_bytes();proof=json.loads((a.directory/'proof.json').read_text())
    if a.joint:
        import pq384_joint_bus as bus
        import pq384_joint_bus_codec as bus_codec
        roots=[bytes.fromhex(v) for v in statement['roots']]
        plain=measure(lambda:bus.verify(proof,spec,roots))
        binary=measure(lambda:bus_codec.decode(wire,spec,roots)==proof)
        shared=measure(lambda:bus_codec.verify_shared(wire,spec,roots))
        scope=f'Actual Q8/Ext4 {len(roots)}-table joint-opening AIR and randomized bus-fingerprint verifier'
    elif a.bus:
        import pq384_global_bus as bus
        import pq384_global_bus_codec as bus_codec
        roots=[bytes.fromhex(v) for v in statement['roots']]
        plain=measure(lambda:bus.verify(proof,spec,roots))
        binary=measure(lambda:bus_codec.decode(wire,spec,roots)==proof)
        shared=measure(lambda:bus_codec.verify_shared(wire,spec,roots))
        scope=f'Actual Q8/Ext4 {len(roots)}-table AIR and randomized bus-fingerprint verifier'
    else:
        root=bytes.fromhex(statement['root'])
        plain=measure(lambda:air.verify_table_local(proof,spec,root))
        binary=measure(lambda:codec.decode(wire,spec,root)==proof)
        scope='Actual Q8/Ext4 single-table verifier only'
    report=dict(status='PASS',proof_sha256=hashlib.sha256(wire).hexdigest(),binary_bytes=len(wire),
        expanded_verifier=plain,binary_decode_authenticate_verify=binary,
        limits=[scope,'Counts include repeated transcript replay and path verification in current implementation',
                'Hash invocation counts are not SHA384 circuit constraints','No recursive prover or recursion soundness established','Profiler timings intentionally omitted'])
    if a.bus or a.joint:report['shared_binary_verifier']=shared
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:{n:v[n] for n in ('total_hash_calls','total_sha384_compression_blocks','ext4_operation_calls')} for k,v in [('expanded',plain),('binary',binary)]},indent=2))
if __name__=='__main__':main()
