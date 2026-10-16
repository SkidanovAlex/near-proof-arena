"""Staged complete multi-table diagnostic, fresh SHA384-challenge auxiliaries."""
import argparse,contextlib,hashlib,json,os,subprocess,sys,time
from pathlib import Path

def choose_packing(n,width):
    p=1
    while (1<<n)*p<128 or (width+p-1)//p>64:p*=2
    if (1<<n)*p>262144:raise ValueError('unsupported table packing')
    return p

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--spec',required=True)
    ap.add_argument('--source-directory',required=True);ap.add_argument('--source-pattern',default='source-{index:02d}-rows.json')
    ap.add_argument('--rs-binary',required=True);ap.add_argument('--folded-library',required=True);ap.add_argument('--fft-library',required=True)
    ap.add_argument('--source-zero-cache');ap.add_argument('--output-dir',required=True);a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_gkr_bus as bus
    from pq384_native_fft import NativeFFT
    from native_folded_v2 import library
    from pq384_source_cache import SourceCache
    from packed_claim_handoff import packing_context
    original=json.loads(Path(a.spec).read_text());tables=original['air']['tables'];out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True)
    spec={k:original[k] for k in ('air','public','log_rows')};spec.update(terminal_degree=1,
        source_packings=[choose_packing(n,t['width']) for n,t in zip(spec['log_rows'],tables)],
        aux_packings=[choose_packing(n,4*bus.aux.layout(t)['aux_columns']) if bus.aux.layout(t)['aux_columns'] else 0 for n,t in zip(spec['log_rows'],tables)])
    if 'source_packings' in original:
        spec['source_packings']=original['source_packings'];spec['aux_packings']=original['aux_packings']
    if a.source_zero_cache:spec['source_packings'][0]=json.loads((Path(a.source_zero_cache)/'manifest.json').read_text())['packing']
    bus.validate(spec);roots=[];source_caches=[];started=time.perf_counter();timing={};source_hashes=[]
    def save(path,value):path.write_text(json.dumps(value,separators=(',',':')));return path
    def commit(rows,packing,label):
        cache=out/(label+'-cache');inp=out/(label+'-commit-input.json');result=out/(label+'-commit-output.json')
        value={'rows':rows,'packing':packing,'indices':[],'cache_directory':str(cache)}
        raw=json.dumps(value,separators=(',',':')).encode();digest=hashlib.sha256(raw).hexdigest();marker=out/(label+'-input.sha256')
        if cache.exists():
            if not marker.exists() or marker.read_text()!=digest:raise ValueError('cache input changed')
        else:
            inp.write_bytes(raw);subprocess.run([a.rs_binary,str(inp),str(result)],check=True,capture_output=True)
            marker.write_text(digest);inp.unlink()
        m=json.loads((cache/'manifest.json').read_text());return cache,bytes.fromhex(m['root_hex'])
    def source(ti):
        path=Path(a.source_directory)/a.source_pattern.format(index=ti)
        raw=path.read_bytes();return json.loads(raw)['rows'],hashlib.sha256(raw).hexdigest()
    for ti,table in enumerate(tables):
        rows,digest=source(ti);source_hashes.append(digest)
        if ti==0 and a.source_zero_cache:
            cache=Path(a.source_zero_cache);m=json.loads((cache/'manifest.json').read_text());root=bytes.fromhex(m['root_hex'])
            # Explicit reuse is prover data; all claims remain authenticated later.
        else:cache,root=commit(rows,spec['source_packings'][ti],f'source-{ti:02d}')
        with SourceCache(cache,expected_root=root,log_rows=spec['log_rows'][ti],width=table['width'],packing=spec['source_packings'][ti]):pass
        source_caches.append(cache);roots.append(root)
        print(f'source commitment {ti+1}/{len(tables)}',flush=True)
    timing['source_commitments']=time.perf_counter()-started
    st,t,alpha,gamma=bus.begin(spec,roots);aux_roots=[];aux_caches=[];finals=[];started=time.perf_counter()
    save(out/'statement.json',dict(spec=spec,roots=[r.hex() for r in roots]))
    for ti,table in enumerate(tables):
        rows,_=source(ti)
        generated=bus.aux.generate(table,rows,spec['public'],alpha,gamma)
        coords=[[x for value in row for x in value] for row in generated['aux_rows']]
        fs=[list(v) for v in generated['finals']];finals.append(fs)
        save(out/f'new-aux-{ti:02d}-rows.json',{'rows':coords})
        if bus.aux.layout(table)['aux_columns']:
            cache,root=commit(coords,spec['aux_packings'][ti],f'aux-{ti:02d}')
        else:cache=None;root=bus.empty_aux_root(spec,ti,st)
        aux_caches.append(cache);aux_roots.append(root)
        print(f'fresh auxiliary {ti+1}/{len(tables)}',flush=True)
    timing['fresh_auxiliaries_and_commitments']=time.perf_counter()-started
    bus.initialize_aux(t,spec,aux_roots,finals)
    rounds=[];terminals=[];private_rows=[];table_timings=[];lib=library(a.folded_library)
    save(out/'fresh-bus-challenges.json',dict(alpha=alpha,gamma=gamma,finals=finals))
    for ti,table in enumerate(tables):
        rows,_=source(ti);coords=json.loads((out/f'new-aux-{ti:02d}-rows.json').read_text())['rows'];started=time.perf_counter()
        rd,terminal,private=bus.constraint_prove(spec,t,alpha,gamma,ti,rows,coords,finals[ti],lib)
        rounds.append(rd);terminals.append(terminal);private_rows.append(private);table_timings.append(time.perf_counter()-started)
        print(f'zerocheck table {ti+1}/{len(tables)}',flush=True)
    started=time.perf_counter()
    with contextlib.ExitStack() as stack:
        caches=[]
        for ti,table in enumerate(tables):
            caches.append(stack.enter_context(SourceCache(source_caches[ti],expected_root=roots[ti],log_rows=spec['log_rows'][ti],width=table['width'],packing=spec['source_packings'][ti])))
            if aux_caches[ti]:caches.append(stack.enter_context(SourceCache(aux_caches[ti],expected_root=aux_roots[ti],log_rows=spec['log_rows'][ti],width=4*bus.aux.layout(table)['aux_columns'],packing=spec['aux_packings'][ti])))
        proof=bus.finish_prove(spec,roots,aux_roots,finals,st,t,alpha,gamma,rounds,terminals,private_rows,caches,NativeFFT(a.fft_library))
    timing['gkr_and_weighted_pcs']=time.perf_counter()-started
    save(out/'proof.json',proof);env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir])
    started=time.perf_counter();result=subprocess.run([sys.executable,str(Path(bus.__file__)),str(out/'proof.json'),str(out/'statement.json')],env=env,check=True,capture_output=True,text=True)
    timing['independent_verifier']=time.perf_counter()-started
    report=dict(status='PASS',tables=len(tables),source_hashes=source_hashes,source_packings=spec['source_packings'],aux_packings=spec['aux_packings'],
        timing=timing,table_timings=table_timings,proof_json_bytes=(out/'proof.json').stat().st_size,verification=result.stdout.strip(),
        scope='Complete local AIR and randomized bus-fingerprint product check; exact natural balance conditional on bad-event exclusions',
        limits=['Q8/Ext4 diagnostic; no certified proximity/RBR/QROM/128-bit security','Fresh auxiliaries depend on new SHA384 challenges'])
    report.update(profile=bus.PROFILE,source_spec_path=str(Path(a.spec).resolve()),
        source_spec_sha256=hashlib.sha256(Path(a.spec).read_bytes()).hexdigest(),
        statement_sha256=hashlib.sha256((out/'statement.json').read_bytes()).hexdigest(),
        proof_sha256=hashlib.sha256((out/'proof.json').read_bytes()).hexdigest(),
        canonical_statement_digest=st.hex(),reused_source_table_indices=[0] if a.source_zero_cache else [],
        source_cache_directories=[str(p) for p in source_caches],
        auxiliary_cache_directories=[str(p) if p is not None else None for p in aux_caches])
    save(out/'report.json',report);print(json.dumps(report,indent=2))

if __name__=='__main__':main()
