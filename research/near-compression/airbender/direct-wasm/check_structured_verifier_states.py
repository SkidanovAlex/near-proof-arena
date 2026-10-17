"""Full retained verifier shadow: compare every coefficient after each state update.
Dense reference protocol, transcript and accepted wire remain unchanged.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import time
from unittest.mock import patch
import pq384_ext8_reference as f
from pq384_ext8_native import Kernel
import pq384_ext8_weighted as pcs
import ext8_switch_execution_codec as codec
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import contract
from ext8_structured_functional import Functional

ROOT=Path(__file__).resolve().parents[2]


class Shadow(Kernel):
    def __init__(self,path):
        super().__init__(path);self.reference=Kernel(path);self.state=None;self.last=None;self.events=[]
        self.dense_injection_terms=0;self.structured_fold_terms=0;self.compared=0
    def begin(self,point):
        if self.state is not None:raise ValueError('unexpected second initial functional')
        self.state=Functional.equality(point);self.last=original_eqs(point)
        self.check(self.last,'initial');return self.last
    def materialize(self):
        s=self.state;weights=[f.mul(s.tensor_scale,x) for x in original_eqs(s.point)]
        if s.powers:
            mixers,points=zip(*s.powers)
            weights,_=self.reference.inject(weights,f.ZERO,points,[f.ZERO]*len(points),mixers)
        return weights
    def check(self,actual,kind):
        expected=self.materialize();actual=[tuple(x) for x in actual]
        if expected!=actual:raise ValueError('structured '+kind+' state mismatch')
        # Independent Python point evaluation checks endpoints even when full
        # materialization reuses the tested native injection primitive.
        for i in sorted({0,len(actual)//2,len(actual)-1}):
            if self.state.at(i)!=actual[i]:raise ValueError('point evaluation mismatch')
        self.compared+=len(actual);self.last=actual
        self.events.append(dict(kind=kind,degree=len(actual),geometric_terms=len(self.state.powers),
            expanded_payload_bytes=32*len(actual),structured_scalar_payload_bytes=32*(len(self.state.point)+1+2*len(self.state.powers))))
        print('Checked '+kind+' degree '+str(len(actual))+' terms '+str(len(self.state.powers)),flush=True)
    def input_check(self,values):
        if self.state is None or [tuple(x) for x in values]!=self.last:raise ValueError('unexpected dense state input')
    def affine_fold(self,values,r):
        self.input_check(values);actual=super().affine_fold(values,r)
        self.structured_fold_terms+=len(self.state.powers);self.state=self.state.fold(r);self.check(actual,'fold');return actual
    def inject(self,weights,claim,points,answers,mixers):
        self.input_check(weights);actual,new_claim=super().inject(weights,claim,points,answers,mixers)
        expected=f.canonical(claim)
        for m,a in zip(mixers,answers):expected=f.add(expected,f.mul(f.canonical(m),f.canonical(a)))
        if new_claim!=expected:raise ValueError('injected claim mismatch')
        self.dense_injection_terms+=len(weights)*len(points);self.state=self.state.inject(points,mixers)
        self.check(actual,'inject');return actual,new_claim


original_eqs=pcs.eqs


def main():
    p=argparse.ArgumentParser();p.add_argument('--native-library',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    base=ROOT/'results/ext8-switch-execution-q309'
    paths=dict(compression=base/'compression.bin',statement=base/'statement.json.gz',config=base/'config.json',receipt=ROOT/'results/ext8-affine-q309/receipt.json',calls=ROOT/'results/ext8-linked-calls/calls.json',call_proof=ROOT/'results/call-ext8-shared-q309/proof.bin')
    def read(p):
        raw=p.read_bytes();return json.loads(gzip.decompress(raw) if p.suffix=='.gz' else raw)
    statement,receipt,expected,config=[read(paths[k]) for k in ('statement','receipt','calls','config')]
    native=Shadow(a.native_library);start=time.monotonic()
    contract(statement,receipt);calls.decode(paths['call_proof'].read_bytes(),statement,receipt,expected,queries=309)
    with patch.object(pcs,'eqs',native.begin):
        codec.decode(paths['compression'].read_bytes(),statement['spec'],statement['roots'],config=config,native=native)
    assert sum(e['kind']=='fold' for e in native.events)==17 and sum(e['kind']=='inject' for e in native.events)==7
    report=dict(status='FULL_VERIFIER_STRUCTURED_STATE_PARITY',fresh_verifier_passed=True,events=native.events,
        compared_ext8_coefficients=native.compared,dense_injection_coefficient_terms=native.dense_injection_terms,
        structured_geometric_term_fold_updates=native.structured_fold_terms,instrumented_seconds=time.monotonic()-start,
        scope='Original complete retained fixture verifies. All coefficients at initial state and all17fold/7injection transitions equal a structured shadow. Full expansion uses the existing native injection kernel on transformed geometric terms; independent Python at() checks three positions per state and small sequence tests cover full Python expansion. No transcript change, measured verifier speedup, complete compiler refinement, PQ128 or recursive proof. Structured state can exceed dense terminal size; a hybrid representation is appropriate.',
        input_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths.values()},
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('ext8_structured_functional.py'),Path(__file__).with_name('pq384_ext8_native.py'),Path(codec.__file__)]},native_library_sha256=hashlib.sha256(a.native_library.read_bytes()).hexdigest())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('events','input_sha256','source_sha256')},indent=2))


if __name__=='__main__':main()
