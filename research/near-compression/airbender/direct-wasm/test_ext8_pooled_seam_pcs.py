"""Actual mixed-height seam committed as one bank and opened by pooled PCS.
The external functional descriptor is fixed by this diagnostic fixture. This
is not execution/GKR-to-bank root mapping or a complete NEAR proof.
"""
import argparse,hashlib,json,subprocess,sys,tempfile,time
from pathlib import Path
import pq384_ext8_weighted as p
import pq384_ext8_weighted_codec as c
import pq384_ext8_weight_families as family
import ext8_pooled_weights as pool
from pq384_ext8_native import Kernel
from test_ext8_pooled_seam import load_seam


def main():
    ap=argparse.ArgumentParser()
    for key in ('source-directory','opening','capture','output'):ap.add_argument('--'+key,type=Path,required=True)
    ap.add_argument('--queries',type=int,default=309);a=ap.parse_args();started=time.perf_counter()
    rows,terms,source_hashes,opening_hash=load_seam(a.source_directory,a.opening)
    claim=pool.coefficient_claim(rows,terms,128);assert claim==pool.direct_claim(rows,terms)
    st=p.h.hash_parts(b'ext8-pooled-seam-fixture-v1',json.dumps(source_hashes).encode(),bytes.fromhex(opening_hash))
    parent=p.h.hash_parts(b'ext8-pooled-seam-parent',st)
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory(prefix='pooled-seam-pcs-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True);native=Kernel(lib)
        start=time.perf_counter();cache=p.Source(rows,128,native);commit_seconds=time.perf_counter()-start
        branches=[dict(root=cache.root.hex(),log_rows=11,width=128,packing=128,terms=terms)]
        print('Committed actual mixed-height seam bank',flush=True)
        start=time.perf_counter();proof=p.prove([cache],native,st,parent,branches,claim,queries=a.queries);prove_seconds=time.perf_counter()-start
        assert proof['profile']==family.POOLED_PROFILE
        wire=json.loads(json.dumps(proof));assert p.verify(wire,st,parent,branches,claim,queries=a.queries)
        binary=c.encode(wire,st,parent,branches,claim,queries=a.queries,derived_folds=True)
        assert c.decode(binary,st,parent,branches,claim,queries=a.queries)==wire
        assert c.verify(binary,st,parent,branches,claim,queries=a.queries)
        a.capture.mkdir(parents=True,exist_ok=True)
        (a.capture/'proof.json').write_text(json.dumps(wire,separators=(',',':')))
        (a.capture/'proof.bin').write_bytes(binary)
        cfg=dict(statement=st.hex(),parent=parent.hex(),branches=branches,claim=claim,queries=a.queries)
        (a.capture/'opening.json').write_text(json.dumps(cfg,separators=(',',':')))
        fresh=subprocess.run([sys.executable,str(Path(p.__file__)),str(a.capture)],check=True,capture_output=True,text=True)
        (a.capture/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr)
        report=dict(status='PASS',profile=proof['profile'],queries=a.queries,physical_bank=dict(rows=2048,width=128,packing=128,degree=cache.degree,lanes=cache.lanes,root=cache.root.hex()),
                    logical_terms=[dict(rows=1<<len(t['row_point']),offset=t['offset'],width=t['width']) for t in terms],
                    native_states_per_bank_lane=1,proof_bytes=len(binary),commit_seconds=commit_seconds,prove_seconds=prove_seconds,total_seconds=time.perf_counter()-started,
                    fresh_verifier=fresh.stdout.strip(),source_sha256=source_hashes,opening_sha256=opening_hash,proof_sha256=hashlib.sha256(binary).hexdigest(),
                    scope='One actual 2048x128 mixed-height seam PCS opening. Not the full pooled source/auxiliary bank, complete execution proof, full NEAR or PQ128 soundness certificate.')
        a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
