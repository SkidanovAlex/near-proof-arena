"""Count executed Python Ext8 operations and native vector calls in full fixture.
Includes function aliases via code-object profiling. Native scalar work excluded.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
import pq384_ext8_reference as f
import pq384_ext8_native as native_module
import pq384_primitives as h
import ext8_switch_execution_codec as codec
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import contract

ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--native-library',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    base=ROOT/'results/ext8-switch-execution-q309'
    paths=dict(compression=base/'compression.bin',statement=base/'statement.json.gz',config=base/'config.json',receipt=ROOT/'results/ext8-affine-q309/receipt.json',calls=ROOT/'results/ext8-linked-calls/calls.json',call_proof=ROOT/'results/call-ext8-shared-q309/proof.bin')
    def read(path):
        raw=path.read_bytes();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
    statement,receipt,expected,config=[read(paths[k]) for k in ('statement','receipt','calls','config')]
    wire,call_wire=paths['compression'].read_bytes(),paths['call_proof'].read_bytes()
    native=native_module.Kernel(a.native_library)
    field_codes={value.__code__:name for name,value in vars(f).items() if callable(value) and hasattr(value,'__code__')}
    native_codes={value.__code__:name for name,value in vars(native_module.Kernel).items() if callable(value) and hasattr(value,'__code__') and name not in ('__init__','pack','unpack')}
    counts={};stage='';started=time.monotonic()
    def profile(frame,event,arg):
        if event!='call':return
        code=frame.f_code;counter=counts[stage]
        if code in field_codes:counter['ext8/'+field_codes[code]]+=1
        elif code==h.hash_parts.__code__:counter['hash_parts']+=1
        elif code in native_codes:
            name=native_codes[code];counter['native/'+name]+=1
            for key in ('values','weights','points','coefficients','words'):
                value=frame.f_locals.get(key)
                if isinstance(value,(list,tuple)):counter['native/'+name+'/'+key+'_elements']+=len(value)
    for label,fn in [('contract',lambda:contract(statement,receipt)),('call_link',lambda:calls.decode(call_wire,statement,receipt,expected,queries=309)),('compression',lambda:codec.decode(wire,statement['spec'],statement['roots'],config=config,native=native))]:
        stage=label;counts[stage]=Counter();start=time.monotonic();sys.setprofile(profile)
        try:fn()
        finally:sys.setprofile(None)
        print(label+' verified in '+str(round(time.monotonic()-start,3))+'s',flush=True)
    census=read(ROOT/'results/switch-full-verifier-hash-work.json')
    assert sum(c['hash_parts'] for c in counts.values())==census['measurement']['totals']['calls']
    report=dict(status='FULL_FIXTURE_ARITHMETIC_CALLS_MEASURED',fresh_verifier_passed=True,stages={k:dict(sorted(v.items())) for k,v in counts.items()},instrumented_seconds=time.monotonic()-started,
        hash_calls_match_prior_census=True,
        scope='Executed full retained diagnostic fixture contract, call-link and compression verifier. Counts Python reference functions including imported aliases; composite operations also count their nested scalar calls, so do not sum all counters as disjoint gates. Native calls and vector lengths recorded separately; native scalar arithmetic and built-in base-field arithmetic not counted. Not a circuit gate count, formal verifier compiler, full NEAR run, or soundness/security proof.',
        input_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths.values()},
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(f.__file__),Path(native_module.__file__),Path(codec.__file__),Path(calls.__file__),Path(h.__file__)]},native_library_sha256=hashlib.sha256(a.native_library.read_bytes()).hexdigest())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report['stages'],indent=2))


if __name__=='__main__':main()
