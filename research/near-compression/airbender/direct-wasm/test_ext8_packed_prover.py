"""Whole proof equality against reference with heterogeneous sources."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import pq384_ext8_packed_prover as packed
from pq384_ext8_native import Kernel
import pq384_ext8_weighted_codec as codec
from test_ext8_input_weights import coefficient_claim

ROOT=Path(__file__).resolve().parents[2]


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--native-library',required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    rng=random.Random(938709);f=packed.f;p=packed.p;native=Kernel(a.native_library);cases=[]
    scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8))
    for shapes in [[(2,3,2),(3,2,2)],[(4,7,4),(3,2,2)],[(3,1,1)]]:
        caches=[];branches=[];claim=f.ZERO
        for n,width,packing in shapes:
            rows=[[rng.randrange(f.P) for _ in range(width)] for _ in range(1<<n)]
            cache=p.Source(rows,packing,native);caches.append(cache)
            lanes=[[[scalar() if j*packing+c<width else f.ZERO for c in range(packing)] for _ in range(2)] for j in range(cache.lanes)]
            branch=dict(root=cache.root.hex(),log_rows=n,width=width,packing=packing,row_point=[scalar() for _ in range(n)],lanes=lanes)
            branches.append(branch);claim=f.add(claim,coefficient_claim(rows,branch))
        old=p.prove(caches,native,b'packed-test',b'parent',branches,claim,queries=8)
        new=packed.prove(caches,native,b'packed-test',b'parent',branches,claim,queries=8)
        assert old==new and p.verify(new,b'packed-test',b'parent',branches,claim,queries=8)
        wires=[codec.encode(x,b'packed-test',b'parent',branches,claim,queries=8,shared_sources=True) for x in (old,new)]
        assert wires[0]==wires[1]
        cases.append(dict(shapes=shapes,proof_bytes=len(wires[0]),byte_identical=True))
    words=packed.Packed.base(range(1024));assert len(words.words)*words.words.itemsize==32768
    bad=packed.Packed.base(range(4));bad.words[0]=f.P
    try:packed.PackedKernel(native).quadratic(bad,bad)
    except ValueError:pass
    else:raise AssertionError('noncanonical native input accepted')
    report=dict(status='PACKED_PCS_PROOF_BYTE_PARITY',cases=cases,packed_scalar_payload_bytes=32,
        native_noncanonical_rejected=True,scope='Three small complete proofs equal reference objects and compact bytes with fresh verification. Packed input-state payload only; excludes source caches, Python overhead, GKR, trees and full-scale peak RAM. No protocol/security change.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(packed.__file__),Path(p.__file__),Path(codec.__file__)]})
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
