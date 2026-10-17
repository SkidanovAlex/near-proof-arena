"""Ext8 native transcript proof vs Python verifier; input opening remains required."""
import argparse, copy, hashlib, json, random, subprocess, sys, tempfile, time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'generic-air'))
import pq384_ext8_reference as f
import pq384_ext8_terminal_gkr as g
from pq384_ext8_native import Kernel
from pq384_ext8_terminal_compile import compile_ext8_terminal

def dot(a,b):
    value=f.ZERO
    for x,y in zip(a,b):value=f.add(value,f.mul(x,y))
    return value

def check(layout,private,statement,k,reference=False):
    claim=g.values(layout,private)[-1][layout['root']]
    start=time.perf_counter();proof,opening=g.prove(layout,statement,private,claim,kernel=k);prove_seconds=time.perf_counter()-start
    wire=json.loads(json.dumps(proof));start=time.perf_counter();verified=g.verify(layout,statement,wire,claim);verify_seconds=time.perf_counter()-start
    assert verified==opening
    assert dot(private,opening['private_weights'])==opening['private_claim']
    if reference:
        reference_proof,reference_opening=g.prove(layout,statement,private,claim)
        assert proof==reference_proof and opening==reference_opening
    return proof,claim,dict(layers=len(proof['layers']),rounds=sum(len(p['rounds']) for p in proof['layers']),
        raw_gkr_scalar_bytes=32*sum(3*len(p['rounds'])+2 for p in proof['layers']),
        prove_seconds=prove_seconds,verify_seconds=verify_seconds,
        proof_sha256=hashlib.sha256(json.dumps(proof,sort_keys=True).encode()).hexdigest())

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--full',action='store_true');args=ap.parse_args()
    rng=random.Random(819821)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory(prefix='ext8-terminal-gkr-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True);k=Kernel(lib)
        layout=dict(input_size=8,private_capacity=4,constants={4:scalar(),5:f.ZERO,6:f.ONE,7:f.ZERO},
            layers=[[('add',0,1),('sub',1,2),('mul',2,3),('add',4,0),('mul',6,1),('sub',3,4),('add',5,7),('mul',0,4)],
                    [('mul',0,1),('add',2,3),('sub',4,5),('add',6,7)],
                    [('add',0,1),('mul',2,3)]],root=1)
        private=[scalar() for _ in range(4)];statement=b'ext8-gkr-test-circuit'
        proof,claim,small=check(layout,private,statement,k,True)
        mutations=[('round-coefficient',lambda p:p['layers'][0]['rounds'][0][0].__setitem__(0,(p['layers'][0]['rounds'][0][0][0]+1)%f.P)),
            ('noncanonical',lambda p:p['layers'][0]['rounds'][0][0].__setitem__(0,f.P)),
            ('truncated-scalar',lambda p:p['layers'][0]['rounds'][0][0].pop()),
            ('missing-round',lambda p:p['layers'][0]['rounds'].pop()),
            ('wrong-layer-input',lambda p:p['layers'][0]['inputs'][0].__setitem__(0,(p['layers'][0]['inputs'][0][0]+1)%f.P)),
            ('missing-layer',lambda p:p['layers'].pop()),
            ('wrong-profile',lambda p:p.__setitem__('profile','near-pq384-terminal-gkr-v1'))]
        rejected=[]
        for name,mutate in mutations:
            bad=json.loads(json.dumps(proof));mutate(bad)
            try:g.verify(layout,statement,bad,claim)
            except ValueError:rejected.append(name)
            else:raise AssertionError('accepted '+name)
        changed=copy.deepcopy(layout);changed['constants'][4]=f.add(changed['constants'][4],f.ONE)
        for name,ly,st,cl in [('statement',layout,b'changed',claim),('claim',layout,statement,f.add(claim,f.ONE)),('public-circuit',changed,statement,claim)]:
            try:g.verify(ly,st,proof,cl)
            except ValueError:rejected.append(name)
            else:raise AssertionError('accepted '+name)
        try:g.prove(layout,statement,private,f.add(claim,f.ONE),kernel=k)
        except ValueError:rejected.append('false-prover-claim')
        else:raise AssertionError('false output claim accepted')
        full=None
        if args.full:
            path=Path('results/pq384-literal193-gkr-fixed13/statement.json');spec=json.loads(path.read_text())['spec']
            alpha,gamma,rho=scalar(),scalar(),scalar()
            finals=[[scalar() for _ in table['interactions']] for table in spec['air']['tables']]
            terminals=[dict(point=[scalar() for _ in range(n)],tau=[scalar() for _ in range(n)],mixing=scalar(),claim=scalar()) for n in spec['log_rows']]
            circuit=compile_ext8_terminal(spec,alpha,gamma,finals,terminals,rho);layout=g.layer_circuit(circuit)
            private=[f.ZERO]*layout['private_capacity']
            _,_,full=check(layout,private,hashlib.sha384(path.read_bytes()).digest(),k)
            full['statement_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
        report=dict(status='PASS',small=small,exact_reference_proof=True,rejections=rejected,compiled193=full,
            source_sha256={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in ('pq384_ext8_terminal_gkr.py','pq384_ext8_native.py')},
            scope='Transcript-driven Ext8 terminal GKR diagnostic. Python verifier agrees with native prover and direct private-input obligation. Compiled193 uses synthetic terminal data and zero private vector, not a valid state-transition witness. No PCS discharge, Rust refinement, full state proof or quantum security certification.')
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
if __name__=='__main__':main()
