"""Ext8 execution prover with optional complete PCS and external trace fixture."""
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
from pq384_ext8_input_weights import opening_branches
from test_ext8_input_weights import coefficient_claim
import pq384_ext8_weighted as pcs
import ext8_terminal_profiles as profiles

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--pcs-queries',type=int);ap.add_argument('--capture-dir',type=Path)
    ap.add_argument('--statement',type=Path);ap.add_argument('--source-directory',type=Path);ap.add_argument('--compression-receipt',type=Path);ap.add_argument('--terminal-profile',choices=profiles.PROFILES,default='baseline');args=ap.parse_args()
    if (args.statement is None)!=(args.source_directory is None):ap.error('--statement and --source-directory must be supplied together')
    fixture=Path('results/pq384-literal193-gkr-fixed13')
    statement_path=args.statement or fixture/'statement.json'
    statement=json.loads(statement_path.read_text());spec=statement['spec'];rows=[];digests=[]
    if args.compression_receipt:
        from verify_sha384_node_chunk import contract
        contract(statement,json.loads(args.compression_receipt.read_text()))
    if args.source_directory:
        raw_sources=[(args.source_directory/f'source-{i:02d}-rows.json').read_bytes() for i in range(len(spec['air']['tables']))]
        expected=[hashlib.sha256(raw).hexdigest() for raw in raw_sources]
    else:
        expected=json.loads((fixture/'prover-report.json').read_text())['source_hashes']
        raw_sources=[gzip.decompress(Path(f'results/ext8-source193/source-{i:02d}.json.gz').read_bytes()) for i in range(len(expected))]
    for raw,digest in zip(raw_sources,expected):
        assert hashlib.sha256(raw).hexdigest()==digest
        rows.append(json.loads(raw)['rows']);digests.append(hash_parts(b'ext8-diagnostic-source-vector',raw))
    del raw_sources
    print('Loaded source shapes '+str([(len(r),len(r[0])) for r in rows]),flush=True)
    source=Path(__file__).with_name('native-folded')/'kernel_ext8_local.rs'
    source_caches=aux_caches=None
    if args.pcs_queries is not None:
        with tempfile.TemporaryDirectory(prefix='ext8-source-commit-') as tmp:
            libpath=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(libpath)],check=True)
            native=Kernel(libpath)
            source_caches=[]
            for ti,(rs,packing) in enumerate(zip(rows,spec['source_packings'])):
                source_caches.append(pcs.Source(rs,packing,native));print('Committed source '+str(ti),flush=True)
        digests=[c.root for c in source_caches]
        retained=statement['roots']
        assert [x.hex() for x in digests]==retained
    st=hash_parts(b'ext8-execution-reduction-diagnostic-v1',json.dumps(spec,sort_keys=True).encode(),*digests)
    def begin():
        t=Transcript(st);alpha,gamma=local.draw(t,2);return t,alpha,gamma
    print('Source roots checked; generating Ext8 auxiliaries',flush=True)
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
    if args.pcs_queries is not None:
        # Reuse loaded library; ctypes keeps the image mapped after temp unlink.
        aux_caches=[pcs.Source(rs,packing,native) for rs,packing in zip(coordinates,spec['aux_packings'])]
        aux_binding=hash_parts(b'ext8-packed-auxiliary-roots',*[c.root for c in aux_caches],gkr.vector_bytes([v for fs in finals for v in fs]))
    print('Auxiliary commitments complete',flush=True)
    t.commit(b'ext8-all-auxiliary-data',aux_binding)
    source=Path(__file__).with_name('native-folded')/'kernel_ext8_local.rs'
    with tempfile.TemporaryDirectory(prefix='ext8-execution-') as tmp:
        libpath=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(libpath)],check=True)
        lib=library(libpath);kernel=Kernel(libpath);proofs=[];terminals=[];private_rows=[];start=time.perf_counter()
        for ti in range(len(rows)):
            proof,terminal,private=local.prove(spec,t,alpha,gamma,ti,rows[ti],coordinates[ti],finals[ti],lib)
            proofs.append(proof);terminals.append(terminal);private_rows.append(private)
            print('Local table proved '+str(ti),flush=True)
        local_seconds=time.perf_counter()-start
        vt,va,vg=begin();assert (va,vg)==(alpha,gamma);vt.commit(b'ext8-all-auxiliary-data',aux_binding)
        checked=[local.verify(spec,vt,ti,json.loads(json.dumps(proof))) for ti,proof in enumerate(proofs)]
        assert checked==terminals
        rho=local.draw(t)[0];assert local.draw(vt)[0]==rho
        circuit=profiles.apply(compile_ext8_terminal(spec,alpha,gamma,finals,terminals,rho),args.terminal_profile);layout=gkr.layer_circuit(circuit)
        private=[f.ZERO]*circuit['private_input_capacity']
        for block in circuit['input_blocks']:
            cur,nxt=private_rows[block['table']];offset=block['offset'];width=block['column_capacity']
            private[offset:offset+len(cur)]=cur;private[offset+width:offset+width+len(nxt)]=nxt
        # Crucially require zero: terminals now come from valid local proofs.
        start=time.perf_counter();gp,opening=gkr.prove(layout,t.seed,private,f.ZERO,kernel=kernel);gkr_seconds=time.perf_counter()-start
        print('GKR proved',flush=True)
        verified=gkr.verify(layout,vt.seed,json.loads(json.dumps(gp)),f.ZERO);assert verified==opening
        value=f.ZERO
        for x,w in zip(private,verified['private_weights']):value=f.add(value,f.mul(x,w))
        assert value==verified['private_claim']
        branches=opening_branches(spec,terminals,circuit,verified['private_weights'])
        coefficient_total=f.ZERO
        for branch in branches:
            data=(rows if branch['branch']==0 else coordinates)[branch['table']]
            coefficient_total=f.add(coefficient_total,coefficient_claim(data,branch))
        assert coefficient_total==verified['private_claim']
        pcs_result=None
        if args.pcs_queries is not None:
            opening_caches=[(source_caches if b['branch']==0 else aux_caches)[b['table']] for b in branches]
            opening_branches_bound=[{**{key:value for key,value in b.items() if key not in ('table','branch')},'root':cache.root.hex()} for b,cache in zip(branches,opening_caches)]
            parent=hash_parts(b'ext8-after-gkr',t.seed,json.dumps(gp,sort_keys=True,separators=(',',':')).encode())
            print('Starting weighted PCS',flush=True)
            start=time.perf_counter();op=pcs.prove(opening_caches,kernel,st,parent,opening_branches_bound,verified['private_claim'],queries=args.pcs_queries);prove_time=time.perf_counter()-start
            start=time.perf_counter();assert pcs.verify(json.loads(json.dumps(op)),st,parent,opening_branches_bound,verified['private_claim'],queries=args.pcs_queries);verify_time=time.perf_counter()-start
            if args.capture_dir:
                args.capture_dir.mkdir(parents=True,exist_ok=True)
                (args.capture_dir/'proof.json').write_text(json.dumps(op,separators=(',',':')))
                cfg=dict(statement=st.hex(),parent=parent.hex(),branches=opening_branches_bound,claim=verified['private_claim'],queries=args.pcs_queries)
                (args.capture_dir/'opening.json').write_text(json.dumps(cfg,separators=(',',':')))
                reduction=dict(spec=spec,source_roots=[c.root.hex() for c in source_caches],aux_roots=[c.root.hex() for c in aux_caches],finals=finals,local=proofs,gkr=gp)
                (args.capture_dir/'reduction.json').write_text(json.dumps(reduction,separators=(',',':')))
                fresh=subprocess.run([sys.executable,str(Path(pcs.__file__)),str(args.capture_dir)],check=True,capture_output=True,text=True)
                assert fresh.stdout.strip()=='PASS weighted Ext8 opening'
                import pq384_ext8_weighted_codec as codec
                binary=codec.encode(op,st,parent,opening_branches_bound,verified['private_claim'],queries=args.pcs_queries,shared_sources=True)
                (args.capture_dir/'proof.bin').write_bytes(binary)
                # Verify from the external statement, deriving all opening parameters.
                fresh=subprocess.run([sys.executable,str(Path(__file__).with_name('verify_ext8_execution.py')),
                    '--reduction',str(args.capture_dir/'reduction.json'),'--opening',str(args.capture_dir/'proof.bin'),
                    '--statement',str(statement_path),'--queries',str(args.pcs_queries),'--terminal-profile',args.terminal_profile]+(['--compression-receipt',str(args.compression_receipt)] if args.compression_receipt else []),check=True,capture_output=True,text=True)
                (args.capture_dir/'complete-verifier.log').write_text(fresh.stdout+fresh.stderr)
            pcs_result=dict(queries=args.pcs_queries,verified=True,json_bytes=len(json.dumps(op,separators=(',',':')).encode()),prove_seconds=prove_time,verify_seconds=verify_time,
                source_roots_match_retained=True,commitment_binding='packed source roots before bus challenges; packed auxiliary roots/finals before local challenges')
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
        report=dict(terminal_profile=args.terminal_profile,weighted_pcs=pcs_result,coefficient_opening_target_checked=True,opening_branches=[dict(table=b['table'],branch=b['branch'],width=b['width'],packing=b['packing'],lanes=len(b['lanes'])) for b in branches],corrupted_source_rejected=True,status='PASS',source_sha256=expected,source_rows=[len(r) for r in rows],global_bus_product_equal=True,
            local_rounds=sum(map(len,proofs)),local_scalar_bytes=32*sum(len(cs) for proof in proofs for cs in proof),
            gkr_layers=len(gp['layers']),gkr_scalar_bytes=32*sum(3*len(p['rounds'])+2 for p in gp['layers']),
            zero_terminal_claim_verified=True,direct_private_obligation_checked=True,local_seconds=local_seconds,gkr_seconds=gkr_seconds,
            mutated_local_round_rejected=True,
            scope=('Source hashes recorded and packed commitments match the external statement when PCS enabled. Optional weighted PCS uses retained source roots and fresh auxiliary roots in correct transcript order and verifies the GKR input opening; without it, full-vector diagnostic hashes/direct witness checks remain. This is still a diagnostic protocol, not a formal implementation/proximity/QROM/security certificate. No complete compact envelope measurement.'))
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
if __name__=='__main__':main()
