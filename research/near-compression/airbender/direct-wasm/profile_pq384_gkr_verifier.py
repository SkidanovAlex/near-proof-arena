"""Actual GKR-bus recursive-work inventory, using existing call-level profiler.
Counts include framed SHA384 blocks and exact reference Ext4 calls; not gates.
"""
import argparse,hashlib,json,sys
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--input-directory',required=True);ap.add_argument('--binary',required=True);ap.add_argument('--output',required=True);a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_gkr_bus as bus
    import pq384_compact_gkr_bus_codec as codec
    from profile_pq384_verifier import measure
    inp=Path(a.input_directory);s=json.loads((inp/'statement.json').read_text());proof=json.loads((inp/'proof.json').read_text());roots=[bytes.fromhex(x) for x in s['roots']];data=Path(a.binary).read_bytes()
    expanded=measure(lambda:bus.verify(proof,s['spec'],roots));compact=measure(lambda:codec.decode(data,s['spec'],roots)==proof)
    report=dict(status='PASS',tables=len(roots),binary_bytes=len(data),proof_sha256=hashlib.sha256(data).hexdigest(),statement_sha256=hashlib.sha256((inp/'statement.json').read_bytes()).hexdigest(),
        expanded_verifier=expanded,compact_decode_authenticate_verify=compact,
        limits=['Actual33table fullheight Q8/Ext4 verifier','Counts include current duplicate hashing/authentication and compiler arithmetic','Hash blocks and Ext4 calls are not circuit gate counts','No recursive proof or security claim'])
    Path(a.output).write_text(json.dumps(report,indent=2))
    for label,result in [('expanded',expanded),('compact',compact)]:
        print(label,json.dumps({k:result[k] for k in ('total_hash_calls','total_sha384_compression_blocks','ext4_operation_calls')}))
        print(json.dumps(sorted(result['hash_tags'].items(),key=lambda item:-item[1]['compression_blocks'])[:8]))

if __name__=='__main__':main()
