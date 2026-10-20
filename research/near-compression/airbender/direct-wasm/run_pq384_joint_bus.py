import argparse,contextlib,json,os,subprocess,sys,time
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--input-directory',required=True)
    ap.add_argument('--library',required=True);ap.add_argument('--output-directory',required=True);a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_joint_bus as combined
    import pq384_joint_opening as joint
    from pq384_source_cache import SourceCache
    from pq384_native_fft import NativeFFT
    inp=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True)
    trusted=json.loads((inp/'statement.json').read_text());report=json.loads((inp/'report.json').read_text())
    prefix=json.loads((inp/'proof.json').read_text());spec=trusted['spec'];roots=[bytes.fromhex(v) for v in trusted['roots']]
    for part in prefix['tables']:part['openings']=[None]*len(part['openings'])
    args=combined.arguments(prefix,spec,roots);paths=[]
    for src,aux in zip(report['source_cache_directories'],report['auxiliary_cache_directories']):
        paths.append(src)
        if aux is not None:paths.append(aux)
    start=time.perf_counter()
    with contextlib.ExitStack() as stack:
        caches=[stack.enter_context(SourceCache(path,**{k:arg[k] for k in ('expected_root','log_rows','width','packing')})) for path,arg in zip(paths,args)]
        proof=dict(profile=combined.PROFILE,air=prefix,joint=joint.prove(caches,NativeFFT(a.library),args))
    seconds=time.perf_counter()-start
    (out/'proof.json').write_text(json.dumps(proof,separators=(',',':')));(out/'statement.json').write_text(json.dumps(trusted,separators=(',',':')))
    env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir]);start=time.perf_counter()
    verified=subprocess.run([sys.executable,str(Path(combined.__file__)),str(out/'proof.json'),str(out/'statement.json')],env=env,check=True,capture_output=True,text=True)
    result=dict(status='PASS',tables=len(prefix['tables']),opening_branches=len(args),prover_seconds=seconds,
                verifier_seconds=time.perf_counter()-start,proof_json_bytes=(out/'proof.json').stat().st_size,
                verification=verified.stdout.strip(),scope='AIR/local/bus fingerprint plus experimental joint PCS',
                limits=['New distinct-point sumcheck and adaptive virtual-source soundness unproved','Q8/Ext4; no security certification'])
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
