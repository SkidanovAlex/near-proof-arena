"""Actual old verifier lengths; hypothetical injective byte-wrapper cost only.

Does NOT replace its hashes. New digests, transcript queries and encodings would
change the workload. This is an architectural sensitivity calculation.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
import pq384_primitives as h
import ext8_switch_execution_codec as codec
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import contract
from pq384_ext8_native import Kernel
from measure_ext8_recursive_hash_work import frame
import model_joint_nibble_geometry as geometry

ROOT=geometry.ROOT


def main():
    p=argparse.ArgumentParser();p.add_argument('--native-library',type=Path,required=True);a=p.parse_args()
    base=ROOT/'results/ext8-switch-execution-q309'
    paths=dict(wire=base/'compression.bin',statement=base/'statement.json.gz',config=base/'config.json',
        receipt=ROOT/'results/ext8-affine-q309/receipt.json',calls=ROOT/'results/ext8-linked-calls/calls.json',
        call_proof=ROOT/'results/call-ext8-shared-q309/proof.bin')
    def read(path):
        raw=path.read_bytes();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
    statement,config,receipt,expected=[read(paths[k]) for k in ('statement','config','receipt','calls')]
    wire,call_wire=paths['wire'].read_bytes(),paths['call_proof'].read_bytes();native=Kernel(a.native_library)
    all_lengths=Counter();unique_lengths=Counter();seen=set();tags={}
    def profile(f,event,arg):
        if event!='call' or f.f_code is not h.hash_parts.__code__:return
        raw=frame(f.f_locals['tag'],f.f_locals['parts']);length=len(raw)
        all_lengths[length]+=1
        if raw not in seen:
            seen.add(raw);unique_lengths[length]+=1
            tag=f.f_locals['tag'].decode();row=tags.setdefault(tag,dict(unique_calls=0,framed_bytes=0,hypothetical_permutations=0))
            row['unique_calls']+=1;row['framed_bytes']+=length
            row['hypothetical_permutations']+=(length+1+56)//57
    started=time.monotonic();sys.setprofile(profile)
    try:
        contract(statement,receipt)
        calls.decode(call_wire,statement,receipt,expected,queries=309)
        codec.decode(wire,statement['spec'],statement['roots'],config=config,native=native)
    finally:
        sys.setprofile(None)
    elapsed=time.monotonic()-started
    baseline=json.loads((ROOT/'results/switch-full-verifier-hash-work.json').read_bytes())
    totals=dict(calls=sum(all_lengths.values()),unique_calls=sum(unique_lengths.values()),
        blocks=sum(((n+17+127)//128)*v for n,v in all_lengths.items()),
        unique_blocks=sum(((n+17+127)//128)*v for n,v in unique_lengths.items()))
    assert totals==baseline['measurement']['totals']
    permutation_count=sum(((n+1+56)//57)*v for n,v in unique_lengths.items())
    layout_path=ROOT/'results/poseidon2-permutation-layout/report.json';layout=read(layout_path)
    assert layout['width']==2106 and layout['reported_table_degree']==2
    rows=1<<(permutation_count-1).bit_length();log=rows.bit_length()-1
    projections=[]
    for q in (8,309):
        best=geometry.optimize_packings([rows],[layout['width']],q)
        # One source commitment, no aux; includes local degree2 sumcheck only.
        # The current adapter requires positive auxiliaries: this is not runnable.
        fixed=8+48+32*log*(2+2)
        projections.append(dict(queries=q,**best,optimistic_fixed_bytes=fixed,
            expected_permutation_only_bytes=fixed+best['expected_opening_bytes'],
            packed_base_coefficient_payload_bytes=4*sum(b['degree']*b['lanes'] for b in best['branches']),
            missing_costs=['GKR','sponge chaining, byte canonicalization and padding constraints',
                'logical hash-call/root binding and all nonhash verifier arithmetic','auxiliary/adapter integration'],
            executable_profile=False,security_certified=False))
    pins=[Path(__file__),Path(geometry.__file__),ROOT/'airbender/direct-wasm/measure_ext8_recursive_hash_work.py',
          ROOT/'results/switch-full-verifier-hash-work.json',layout_path]+list(paths.values())
    report=dict(status='OLD_VERIFIER_BYTE_WRAPPER_COUNTERFACTUAL',fresh_original_verifier_passed=True,
        totals=totals,all_input_lengths=dict(sorted(all_lengths.items())),unique_input_lengths=dict(sorted(unique_lengths.items())),
        tags=tags,hypothetical_permutations=permutation_count,padded_permutation_rows=rows,
        logical_permutation_source_cells=permutation_count*layout['width'],projections=projections,
        instrumented_seconds=elapsed,native_library_sha256=hashlib.sha256(a.native_library.read_bytes()).hexdigest(),
        wrapper_shape='Hypothetical width32/rate19/capacity13 sponge; pack3bytes/field, append byte01, pad zeros to3bytes then full19-field blocks. Output13fields requires no extra squeeze. Old framing retained only to price its lengths; no wrapper or protocol implemented.',
        scope='Actual old verifier is replayed unchanged and its complete four-count hash census matches. 57bytes/rate block is a counterfactual injective encoding shape, not a new-transcript measurement. Exact-input dedup requires proved routing. Output52bytes, new domain separation and challenges would change downstream lengths/sharing. Application hashes are not substituted. No quantum security, recursive proof or fullNEAR claim.',
        sha256={str(x.relative_to(ROOT)):hashlib.sha256(x.read_bytes()).hexdigest() for x in pins})
    (ROOT/'results/poseidon2-permutation-layout/workload.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('totals','hypothetical_permutations','padded_permutation_rows','logical_permutation_source_cells','projections')},indent=2))


if __name__=='__main__':main()
