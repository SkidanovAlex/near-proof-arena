"""Ext4 GKR component test; fixed checksum, no authenticated PCS input proof."""
import copy
import gzip
import hashlib
import json
import random
import struct
import subprocess
import tempfile
import time
from pathlib import Path
import pq384_terminal_gkr as g
from pq384_gkr4_native import Kernel
from compile_swirl_fixed_dag import compile_air
from measure_swirl_rebalanced_gkr import merge

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/dag-gkr'


def dot(weights,values):
    assert len(weights)==len(values)
    value=g.ZERO
    for a,b in zip(weights,values):value=g.add(value,g.mul(a,b))
    return value


def main():
    source=ROOT/'results/swirl-security-review/dag-export/dag.jsonl.gz'
    record=merge([json.loads(x) for x in gzip.decompress(source.read_bytes()).splitlines()])
    stats,layout,slots=compile_air(record,reassociate=True,return_artifacts=True)
    rng=random.Random(20261017)
    private=[tuple(rng.randrange(2013265921) for _ in range(4)) for _ in range(layout['private_capacity'])]
    private[len(slots):]=[g.ZERO]*(len(private)-len(slots))
    # Independently evaluate the original, unbalanced exported DAG in Ext4.
    values=[]
    for op,*args in record['nodes']:
        if op in ('variable','first_row','last_row','transition'):v=private[slots[tuple([op,*args])]]
        elif op=='const':v=g.base(args[0])
        elif op=='neg':v=g.sub(g.ZERO,values[args[0]])
        else:v=g.gate(op,values[args[0]],values[args[1]])
        values.append(v)
    outputs=set(record['constraints'])
    for x in record['interactions']:outputs.update([x['count'],*x['message']])
    claim=dot([g.base(i+1) for i in range(len(outputs))],[values[i] for i in sorted(outputs)])
    assert g.values(layout,private)[-1][layout['root']]==claim
    statement=b'nearproof-fixed-dag-component-ext4-v1'
    kernel_source=Path(__file__).with_name('native-folded')/'kernel_gkr4.rs'
    with tempfile.TemporaryDirectory() as tmp:
        lib=Path(tmp)/'kernel.so'
        subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(kernel_source),'-o',str(lib)],check=True)
        start=time.perf_counter();proof,ob=g.prove(layout,statement,private,claim,kernel=Kernel(lib));prover_seconds=time.perf_counter()-start
    start=time.perf_counter();verified=g.verify(layout,statement,proof,claim);verifier_seconds=time.perf_counter()-start
    assert verified==ob and dot(ob['private_weights'],private)==ob['private_claim']
    # The reduction does not itself authenticate an input vector. Demonstrate the
    # obligation detects a changed nonzero-weight slot when explicitly checked.
    index=next(i for i in range(len(slots)) if ob['private_weights'][i]!=g.ZERO)
    changed=private.copy();changed[index]=g.add(changed[index],g.ONE)
    assert dot(ob['private_weights'],changed)!=ob['private_claim']
    rejected=[]
    for change in ('round','claim','statement','layer_count'):
        bad=copy.deepcopy(proof);bad_claim=claim;bad_statement=statement
        if change=='round':bad['layers'][0]['rounds'][0][0]=g.add(bad['layers'][0]['rounds'][0][0],g.ONE)
        elif change=='claim':bad_claim=g.add(claim,g.ONE)
        elif change=='statement':bad_statement=b'wrong-fixed-dag-statement'
        else:bad['layers'].pop()
        try:g.verify(layout,bad_statement,bad,bad_claim)
        except ValueError:rejected.append(change)
        else:raise AssertionError(change)
    elements=[x for part in proof['layers'] for row in part['rounds'] for x in row]
    elements += [x for part in proof['layers'] for x in part['inputs']]
    assert len(elements)==stats['gkr_field_elements']==1198
    raw=b''.join(struct.pack('<4I',*x) for x in elements)
    OUT.mkdir(parents=True,exist_ok=True)
    artifacts={'proof.json':proof,'obligation.json':ob,'layout.json':layout,'inputs.json':private,
               'input-coordinates.json':sorted([(slot,list(key)) for key,slot in slots.items()]),'claim.json':claim}
    pins={}
    for name,value in artifacts.items():
        data=json.dumps(value,separators=(',',':')).encode();(OUT/(name+'.gz')).write_bytes(gzip.compress(data,mtime=0));pins[name]=hashlib.sha256(data).hexdigest()
    (OUT/'field-payload.bin').write_bytes(raw)
    report=dict(status='COMPONENT_PROOF_VERIFIED_WITH_EXPLICIT_INPUT_CHECK',prover_seconds=prover_seconds,
        verifier_seconds=verifier_seconds,extension_degree=4,field_elements=len(elements),field_payload_bytes=len(raw),
        layout=stats,rejected_mutations=rejected,changed_input_rejected_by_obligation=True,raw_sha256=pins,
        source_export_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        limitations=['Ext4 is diagnostic, not PQ128.','Field payload excludes framing, circuit, input-opening proof and other verifier components.',
                    'Fixed output checksum is not sound batching of native verifier constraints.',
                    'Input dot product checked with full witness, not a PCS proof.',
                    'No end-to-end verifier acceptance, NEAR state transition or Lean compiler theorem.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('layout','raw_sha256')}))


def verify_saved():
    def read(name):return json.loads(gzip.decompress((OUT/(name+'.gz')).read_bytes()))
    source=ROOT/'results/swirl-security-review/dag-export/dag.jsonl.gz'
    record=merge([json.loads(x) for x in gzip.decompress(source.read_bytes()).splitlines()])
    _,trusted,slots=compile_air(record,reassociate=True,return_artifacts=True)
    # Circuit is reconstructed from the trusted source, not accepted from proof metadata.
    assert json.loads(json.dumps(trusted))==read('layout.json')
    assert sorted([(slot,list(key)) for key,slot in slots.items()])==[tuple(x) for x in read('input-coordinates.json')]
    ob=g.verify(trusted,b'nearproof-fixed-dag-component-ext4-v1',read('proof.json'),tuple(read('claim.json')))
    private=[tuple(x) for x in read('inputs.json')]
    assert dot(ob['private_weights'],private)==ob['private_claim']
    assert json.loads(json.dumps(ob))==read('obligation.json')
    print('PASS: fresh-process proof verification and full-witness input obligation')


if __name__=='__main__':
    import sys
    if sys.argv[1:]==['--verify-saved']:verify_saved()
    else:main()
