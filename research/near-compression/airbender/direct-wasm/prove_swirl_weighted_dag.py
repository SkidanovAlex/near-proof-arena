"""Weighted terminal-scalar GKR fixture with explicit known/PCS input split.

Controls/selector values are synthetic trusted fixture data, not native-proof
transcript extraction. Remaining PCS obligation is checked with the witness.
"""
import copy,gzip,hashlib,json,random,subprocess,tempfile,time
from pathlib import Path
import pq384_terminal_gkr as g
from pq384_gkr4_native import Kernel
from compile_swirl_fixed_dag import compile_air
from measure_swirl_rebalanced_gkr import merge
from swirl_consumer_weights import terminal_weights,direct_terminal
from prove_swirl_fixed_dag import dot

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/weighted-dag-gkr'


def split_obligation(ob,slots,known):
    """Known values are caller-owned. Unmapped padded slots are fixed to zero."""
    if set(slots.values())!=set(range(len(slots))):raise ValueError('noncanonical slot map')
    if len(ob['private_weights'])<len(slots):raise ValueError('input shape')
    residual=ob['private_claim'];coordinates=[]
    for key,index in sorted(slots.items(),key=lambda x:x[1]):
        w=ob['private_weights'][index]
        is_pcs=key[0]=='variable' and key[1] in (0,1)
        if is_pcs:
            if index in known:raise ValueError('PCS value mislabeled known')
            coordinates.append(dict(coordinate=list(key),slot=index,weight=w))
        else:
            if index not in known:raise ValueError('missing known input')
            residual=g.sub(residual,g.mul(w,known[index]))
    if set(known)!={x for key,x in slots.items() if not(key[0]=='variable' and key[1] in (0,1))}:
        raise ValueError('unexpected known input')
    return dict(claim=residual,coordinates=coordinates,zero_padding_range=[len(slots),len(ob['private_weights'])])


def check_residual_fixture(pcs,private):
    start,end=pcs['zero_padding_range']
    assert len(private)==end and all(x==g.ZERO for x in private[start:end])
    assert dot([x['weight'] for x in pcs['coordinates']],[private[x['slot']] for x in pcs['coordinates']])==pcs['claim']


def fixture():
    source=ROOT/'results/swirl-security-review/dag-export/dag.jsonl.gz'
    records=[json.loads(x) for x in gzip.decompress(source.read_bytes()).splitlines()]
    merged=merge(records)
    stats,layout,slots=compile_air(merged,reassociate=True,public_weights=True,return_artifacts=True)
    rng=random.Random(20261018)
    def rand():return tuple(rng.randrange(2013265921) for _ in range(4))
    controls=dict(lam=rand(),beta=rand(),mu=rand(),eq_ns=[rand() for _ in records],
        eq_sharp=[rand() for _ in records],norms=[rand() for _ in records],
        eq3bs=[[rand() for _ in r['interactions']] for r in records])
    weights,offset=terminal_weights(records,**controls);flat=[x for row in weights for x in row]
    private=[g.ZERO]*layout['private_capacity']
    for key,index in slots.items():private[index]=flat[key[1]] if key[0]=='output_weight' else rand()
    values=[]
    for op,*args in merged['nodes']:
        if op in ('variable','first_row','last_row','transition'):v=private[slots[tuple([op,*args])]]
        elif op=='const':v=g.base(args[0])
        elif op=='neg':v=g.sub(g.ZERO,values[args[0]])
        else:v=g.gate(op,values[args[0]],values[args[1]])
        values.append(v)
    per_air=[];start=0
    for r in records:per_air.append(values[start:start+len(r['nodes'])]);start+=len(r['nodes'])
    native_scalar=direct_terminal(records,per_air,**controls)
    claim=g.sub(native_scalar,offset)
    assert dot(flat,values)==claim and g.values(layout,private)[-1][layout['root']]==claim
    known={index:private[index] for key,index in slots.items() if not(key[0]=='variable' and key[1] in (0,1))}
    # Fixture-owned known inputs and controls are bound before GKR challenges.
    statement=hashlib.sha384(json.dumps(dict(controls=controls,known=known,native_scalar=native_scalar,offset=offset),sort_keys=True).encode()).digest()
    return stats,layout,slots,private,known,claim,statement


def main():
    stats,layout,slots,private,known,claim,statement=fixture()
    with tempfile.TemporaryDirectory() as tmp:
        lib=Path(tmp)/'kernel.so';source=Path(__file__).with_name('native-folded')/'kernel_gkr4.rs'
        subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True)
        start=time.perf_counter();proof,ob=g.prove(layout,statement,private,claim,kernel=Kernel(lib));seconds=time.perf_counter()-start
    assert g.verify(layout,statement,proof,claim)==ob
    pcs=split_obligation(ob,slots,known)
    check_residual_fixture(pcs,private)
    k=next(i for i in known if ob['private_weights'][i]!=g.ZERO)
    changed=known.copy();changed[k]=g.add(changed[k],g.ONE)
    assert split_obligation(ob,slots,changed)['claim']!=pcs['claim']
    missing=known.copy();missing.pop(k)
    try:split_obligation(ob,slots,missing)
    except ValueError:pass
    else:raise AssertionError('missing known input')
    bad=copy.deepcopy(proof);bad['layers'][0]['inputs'][0]=g.add(bad['layers'][0]['inputs'][0],g.ONE)
    try:g.verify(layout,statement,bad,claim)
    except ValueError:pass
    else:raise AssertionError('altered GKR input claim')
    changed_padding=private.copy();changed_padding[len(slots)]=g.ONE
    try:check_residual_fixture(pcs,changed_padding)
    except AssertionError:pass
    else:raise AssertionError('nonzero padded input')
    elements=sum(3*len(p['rounds'])+2 for p in proof['layers']);assert elements==1264
    OUT.mkdir(parents=True,exist_ok=True)
    for name,value in [('proof',proof),('pcs-obligation',pcs),('input-obligation',ob)]:
        (OUT/(name+'.json.gz')).write_bytes(gzip.compress(json.dumps(value).encode(),mtime=0))
    result=dict(status='WEIGHTED_COMPONENT_AND_KNOWN_INPUT_SPLIT_CHECKED',field_elements=elements,
        ext4_field_payload_bytes=elements*16,known_slots=len(known),pcs_coordinates=len(pcs['coordinates']),
        total_input_slots=len(slots),prover_seconds=seconds,negative_checks=4,
        limitations=['Synthetic verifier-owned controls/selectors; no native transcript extraction.',
                    'Residual PCS claim checked with full witness, not a PCS opening proof.',
                    'Ext4 diagnostic only; no PQ128, full NEAR or compiler correctness theorem.'])
    (OUT/'report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))


def replay():
    _,layout,slots,private,known,claim,statement=fixture()
    proof=json.loads(gzip.decompress((OUT/'proof.json.gz').read_bytes()))
    ob=g.verify(layout,statement,proof,claim);pcs=split_obligation(ob,slots,known)
    check_residual_fixture(pcs,private)
    assert json.loads(json.dumps(pcs))==json.loads(gzip.decompress((OUT/'pcs-obligation.json.gz').read_bytes()))
    print('PASS: weighted saved proof and residual PCS functional (full witness)')


if __name__=='__main__':
    import sys
    replay() if sys.argv[1:]==['--verify-saved'] else main()
