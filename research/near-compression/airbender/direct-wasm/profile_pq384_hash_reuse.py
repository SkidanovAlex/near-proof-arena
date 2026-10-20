"""Measure exact repeated hash inputs in the real configured verifier.

This observes calls without caching or modifying verification. Reuse is keyed by
complete bytes, not by a digest; reported savings are compression calls, not gates.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import sys


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--input-directory',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    import pq384_primitives as primitive
    import pq384_seed_gkr_bus as bus
    statement=json.loads((a.input_directory/'statement.json').read_text())
    proof=json.loads((a.input_directory/'proof.json').read_text())
    config=bus.configure(statement['spec']['air'])
    code=primitive.hash_parts.__code__
    seen=set()
    tags=defaultdict(lambda:dict(calls=0,unique_calls=0,blocks=0,unique_blocks=0,unique_framed_bytes=0))
    def observe(frame,event,arg):
        if event!='call' or frame.f_code is not code:return
        tag=frame.f_locals['tag'];parts=frame.f_locals['parts']
        key=(tag,parts)
        length=len(primitive.PREFIX)+4+len(tag)+4+sum(8+len(x) for x in parts)
        blocks=(length+17+127)//128
        row=tags[tag.decode('ascii')];row['calls']+=1;row['blocks']+=blocks
        if key not in seen:
            seen.add(key);row['unique_calls']+=1;row['unique_blocks']+=blocks;row['unique_framed_bytes']+=length
    sys.setprofile(observe)
    try:
        accepted=bus.verify(proof,statement['spec'],[bytes.fromhex(x) for x in statement['roots']],config)
    finally:sys.setprofile(None)
    assert accepted
    totals={k:sum(v[k] for v in tags.values()) for k in ('calls','unique_calls','blocks','unique_blocks','unique_framed_bytes')}
    totals['repeated_blocks']=totals['blocks']-totals['unique_blocks']
    report=dict(status='PASS',profile=proof['profile'],proof_sha256=hashlib.sha256((a.input_directory/'proof.json').read_bytes()).hexdigest(),
        totals=totals,tags=dict(sorted(tags.items())),
        limits=['Trusted configuration setup excluded','Exact (tag, ordered byte parts) equality; no hash-collision assumption for deduplication',
                'Reference execution is unchanged; this is a measurement, not a cached verifier or recursive AIR',
                'A recursive witness must constrain every reused call to the same full input and output; equality/routing costs excluded',
                'Q8/Ext4 diagnostic profile; no security certification'])
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(totals))

if __name__=='__main__':main()
