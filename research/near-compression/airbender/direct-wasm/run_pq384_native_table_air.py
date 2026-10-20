"""Actual table-local SHA384 AIR proof with separately executed Python verifier."""
import argparse,json,os,subprocess,sys,time,hashlib
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True)
    p.add_argument('--spec',required=True);p.add_argument('--source',required=True)
    p.add_argument('--table-index',type=int,required=True);p.add_argument('--cache',required=True)
    p.add_argument('--folded-library',required=True);p.add_argument('--fft-library',required=True)
    p.add_argument('--output-dir',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_table_air as air
    from pq384_native_table_air import prove_native
    from pq384_source_cache import SourceCache
    from pq384_batched_codec import encode
    full=json.loads(Path(a.spec).read_text());rows=json.loads(Path(a.source).read_text())['rows']
    manifest=json.loads((Path(a.cache)/'manifest.json').read_text());root=bytes.fromhex(manifest['root_hex'])
    spec=dict(air=full['air'],public=full['public'],log_rows=full['log_rows'][a.table_index],
              table_index=a.table_index,packing=manifest['packing'])
    table,_=air.validate(spec)
    with SourceCache(a.cache,expected_root=root,log_rows=spec['log_rows'],width=table['width'],packing=spec['packing']) as cache:
        proof,timing=prove_native(spec,root,rows,folded_library=a.folded_library,fft_library=a.fft_library,cache=cache)
    out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True)
    artifact=out/'table-proof.json';artifact.write_text(json.dumps(dict(spec=spec,root=root.hex(),proof=proof),separators=(',',':')))
    (out/'proof.json').write_text(json.dumps(proof,separators=(',',':')))
    (out/'spec.json').write_text(json.dumps(spec,separators=(',',':')))
    binary=encode(proof['opening'],spec['log_rows'],table['width'],spec['packing']);(out/'opening.bin').write_bytes(binary)
    env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir])
    start=time.perf_counter()
    verified=subprocess.run([sys.executable,str(Path(air.__file__)),str(artifact)],env=env,check=True,capture_output=True,text=True)
    timing['separate_verifier_seconds']=time.perf_counter()-start
    report=dict(status='PASS',table_index=a.table_index,rows=len(rows),width=table['width'],
        public_words=len(spec['public']),constraint_degree=air.validate(spec)[1],timing=timing,
        opening_binary_bytes=len(binary),proof_json_bytes=(out/'proof.json').stat().st_size,
        source_root=root.hex(),source_file_sha256=hashlib.sha256(Path(a.source).read_bytes()).hexdigest(),
        spec_sha256=hashlib.sha256((out/'spec.json').read_bytes()).hexdigest(),
        verification=verified.stdout.strip(),
        scope='Actual D1 table-local AIR plus packed source opening; not all33tables or global bus balance',
        limits=['Q8/Ext4 diagnostic; no128-bit or QROM security certification','Spec includes trusted entire public array'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
