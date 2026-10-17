"""Full retained baseline wire with hybrid arithmetic and preserved vector hashes.
Test adapter only: no new protocol, no new proof or production profile change.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import struct
import sys
import time
from unittest.mock import patch
import ext8_closed_hybrid_verify as hybrid
import ext8_closed_derived_switch as closed
import ext8_weighted_code_switch as original
import ext8_code_switch_stage as original_stage
import ext8_switch_execution_codec as codec
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import contract
from pq384_ext8_native import Kernel
from measure_ext8_recursive_hash_work import frame

ROOT=Path(__file__).resolve().parents[2]
_BASELINE=closed._clone(original,__name__+'._baseline')


def baseline_adapter(native,events):
    stage=closed._clone(original_stage,__name__+'._stage')
    def start(config,weights,claim):
        t,_,claim,N,count,omega=original_stage.start(config,weights.expanded(),claim)
        return t,weights,claim,N,count,omega
    stage.start=start;stage.obligation=hybrid.obligation;stage.close_terminal=hybrid.close_terminal
    adapter=closed._clone(_BASELINE,__name__+'._adapter')
    pcs=closed._clone(adapter.pcs,__name__+'._pcs')
    pcs.eqs=lambda point:hybrid.Weights(hybrid.Functional.equality(point),native,events)
    adapter.pcs=pcs;adapter.stage=stage;adapter.initial_obligation=hybrid.initial_obligation
    return adapter


def hybrid_decoder(native,events):
    switch=closed._clone(codec.switch,__name__+'._switch_codec')
    switch.a=baseline_adapter(native,events)
    def decode(data,statement,parent,branches,claim,config,*,native=None):
        return switch.process(data,None,statement,parent,branches,claim,config,hybrid.Backend())[0]
    switch.decode=decode
    return switch


def main():
    p=argparse.ArgumentParser();p.add_argument('--native-library',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    base=ROOT/'results/ext8-switch-execution-q309'
    paths=dict(compression=base/'compression.bin',statement=base/'statement.json.gz',config=base/'config.json',receipt=ROOT/'results/ext8-affine-q309/receipt.json',calls=ROOT/'results/ext8-linked-calls/calls.json',call_proof=ROOT/'results/call-ext8-shared-q309/proof.bin')
    def read(p):
        raw=p.read_bytes();return json.loads(gzip.decompress(raw) if p.suffix=='.gz' else raw)
    statement,receipt,expected,config=[read(paths[k]) for k in ('statement','receipt','calls','config')]
    native=Kernel(a.native_library);events=[];frames=[];index=0;timings={};digest=hashlib.sha256()
    def verify():
        contract(statement,receipt);calls.decode(paths['call_proof'].read_bytes(),statement,receipt,expected,queries=309)
        codec.decode(paths['compression'].read_bytes(),statement['spec'],statement['roots'],config=config,native=native)
    def dense_profile(call,event,arg):
        if event=='call' and call.f_code is hybrid.h.hash_parts.__code__:
            raw=frame(call.f_locals['tag'],call.f_locals['parts']);frames.append(raw)
            digest.update(struct.pack('<Q',len(raw)));digest.update(raw)
    def hybrid_profile(call,event,arg):
        nonlocal index
        if event=='call' and call.f_code is hybrid.h.hash_parts.__code__:
            raw=frame(call.f_locals['tag'],call.f_locals['parts'])
            if index>=len(frames) or raw!=frames[index]:raise ValueError('ordered transcript mismatch at '+str(index))
            index+=1
    started=time.monotonic();sys.setprofile(dense_profile)
    try:verify()
    finally:sys.setprofile(None)
    timings['dense_seconds']=time.monotonic()-started;print('Dense full verifier complete',flush=True)
    started=time.monotonic()
    with patch.object(codec,'switch',hybrid_decoder(native,events)):
        sys.setprofile(hybrid_profile)
        try:verify()
        finally:sys.setprofile(None)
    timings['hybrid_with_required_vector_hashing_seconds']=time.monotonic()-started
    assert index==len(frames)==104839
    assert sum(e['kind']=='fold' for e in events)==17 and sum(e['kind']=='inject' for e in events)==7
    report=dict(status='FULL_RETAINED_HYBRID_VERIFIER_TRANSCRIPT_PARITY',fresh_dense_and_hybrid_verified=True,
        ordered_hash_calls_compared=index,ordered_framed_preimages_sha256=digest.hexdigest(),events=events,timings=timings,
        scope='Same complete retained q309 baseline proof, contract, call-link and compression decoder verified twice. Every ordered framed hash preimage compared literally. Test adapter preserves baseline expanded-vector hash binding; expansions still performed. Timings include asymmetric instrumentation and must not be treated as a production speedup. No new-profile full proof, PQ128/security certificate, Lean implementation refinement or full NEAR claim.',
        input_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths.values()},
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(hybrid.__file__),Path(closed.__file__),Path(original.__file__),Path(original_stage.__file__),Path(codec.__file__),Path(Kernel.__init__.__code__.co_filename)]},native_library_sha256=hashlib.sha256(a.native_library.read_bytes()).hexdigest())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
