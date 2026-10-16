"""Retained prepared execution -> Ext8 local proofs -> GKR; PCS still required."""
import argparse, copy, gzip, hashlib, json, subprocess, sys, tempfile, time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'generic-air'))
import pq384_ext8_reference as f
import pq384_ext8_auxiliary as aux
import pq384_ext8_local as local
import pq384_ext8_terminal_gkr as gkr
from pq384_ext8_terminal_compile import compile_ext8_terminal
from pq384_ext8_local_native import library
from pq384_ext8_native import Kernel
from pq384_primitives import Transcript,hash_parts
from reference import public_messages

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    fixture=Path('results/pq384-literal193-gkr-fixed13');spec=json.loads((fixture/'statement.json').read_text())['spec']
    expected=json.loads((fixture/'prover-report.json').read_text())['source_hashes'];rows=[];digests=[]
    for i,digest in enumerate(expected):
        raw=gzip.decompress(Path(f'results/ext8-source193/source-{i:02d}.json.gz').read_bytes())
        assert hashlib.sha256(raw).hexdigest()==digest
        rows.append(json.loads(raw)['rows']);digests.append(hash_parts(b'ext8-diagnostic-source-vector',raw))
    st=hash_parts(b'ext8-execution-reduction-diagnostic-v1',json.dumps(spec,sort_keys=True).encode(),*digests)
    def begin():
        t=Transcript(st);alpha,gamma=local.draw(t,2);return t,alpha,gamma
    t,alpha,gamma=begin();generated=[aux.generate(table,rs,spec['public'],alpha,gamma) for table,rs in zip(spec['air']['tables'],rows)]
    finals=[x['finals'] for x in generated];coordinates=[[[c for value in row for c in value] for row in x['aux_rows']] for x in generated]
    sends=receives=f.ONE
    for table,fs in zip(spec['air']['tables'],finals):
        for i,value in zip(aux.layout(table)['order'],fs):
            if table['interactions'][i]['send']:sends=f.mul(sends,value)
            else:receives=f.mul(receives,value)
    for bus,send,message in public_messages(spec['air'],spec['public']):
        fp=f.base(bus+1)
        for value in reversed(message):fp=f.add(f.base(value),f.mul(alpha,fp))
        factor=f.sub(gamma,fp)
        if send:sends=f.mul(sends,factor)
        else:receives=f.mul(receives,factor)
    assert sends==receives
    # Full-vector digests preserve challenge chronology for this diagnostic.
    # They are NOT polynomial commitments with authenticated opening evidence.
    aux_binding=hash_parts(b'ext8-diagnostic-aux-vectors',json.dumps(coordinates).encode(),gkr.vector_bytes([v for fs in finals for v in fs]))
    t.commit(b'ext8-all-auxiliary-data',aux_binding)
    source=Path(__file__).with_name('native-folded')/'kernel_ext8_local.rs'
    with tempfile.TemporaryDirectory(prefix='ext8-execution-') as tmp:
        libpath=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(libpath)],check=True)
        lib=library(libpath);kernel=Kernel(libpath);proofs=[];terminals=[];private_rows=[];start=time.perf_counter()
        for ti in range(len(rows)):
            proof,terminal,private=local.prove(spec,t,alpha,gamma,ti,rows[ti],coordinates[ti],finals[ti],lib)
            proofs.append(proof);terminals.append(terminal);private_rows.append(private)
        local_seconds=time.perf_counter()-start
        vt,va,vg=begin();assert (va,vg)==(alpha,gamma);vt.commit(b'ext8-all-auxiliary-data',aux_binding)
        checked=[local.verify(spec,vt,ti,json.loads(json.dumps(proof))) for ti,proof in enumerate(proofs)]
        assert checked==terminals
        rho=local.draw(t)[0];assert local.draw(vt)[0]==rho
        circuit=compile_ext8_terminal(spec,alpha,gamma,finals,terminals,rho);layout=gkr.layer_circuit(circuit)
        private=[f.ZERO]*circuit['private_input_capacity']
        for block in circuit['input_blocks']:
            cur,nxt=private_rows[block['table']];offset=block['offset'];width=block['column_capacity']
            private[offset:offset+len(cur)]=cur;private[offset+width:offset+width+len(nxt)]=nxt
        # Crucially require zero: terminals now come from valid local proofs.
        start=time.perf_counter();gp,opening=gkr.prove(layout,t.seed,private,f.ZERO,kernel=kernel);gkr_seconds=time.perf_counter()-start
        verified=gkr.verify(layout,vt.seed,json.loads(json.dumps(gp)),f.ZERO);assert verified==opening
        value=f.ZERO
        for x,w in zip(private,verified['private_weights']):value=f.add(value,f.mul(x,w))
        assert value==verified['private_claim']
        bad=copy.deepcopy(proofs[0]);bad[0][0]=f.add(bad[0][0],f.ONE)
        bt,_,_=begin();bt.commit(b'ext8-all-auxiliary-data',aux_binding)
        try:local.verify(spec,bt,0,bad)
        except ValueError:pass
        else:raise AssertionError('changed local round accepted')
        corrupted=copy.deepcopy(rows[0]);corrupted[0]=[(x+1)%f.P for x in corrupted[0]]
        bt,_,_=begin();bt.commit(b'ext8-all-auxiliary-data',aux_binding)
        try:local.prove(spec,bt,alpha,gamma,0,corrupted,coordinates[0],finals[0],lib)
        except ValueError as exc:
            assert str(exc)=='invalid trace constraints'
        else:raise AssertionError('corrupted source trace accepted')
        report=dict(corrupted_source_rejected=True,status='PASS',source_sha256=expected,source_rows=[len(r) for r in rows],global_bus_product_equal=True,
            local_rounds=sum(map(len,proofs)),local_scalar_bytes=32*sum(len(cs) for proof in proofs for cs in proof),
            gkr_layers=len(gp['layers']),gkr_scalar_bytes=32*sum(3*len(p['rounds'])+2 for p in gp['layers']),
            zero_terminal_claim_verified=True,direct_private_obligation_checked=True,local_seconds=local_seconds,gkr_seconds=gkr_seconds,
            mutated_local_round_rejected=True,
            scope='Retained execution trace hashes match earlier prepared193 prover report. Fresh Ext8 auxiliaries/local transcript feed a zero-claim GKR proof. Full-vector diagnostic hashes are NOT PCS commitments; final input obligation checked directly against witness. No authenticated PCS discharge, full secure proof size, Rust refinement or quantum security certification.')
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
if __name__=='__main__':main()
