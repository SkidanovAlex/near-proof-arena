"""Run cached full-height global-chain experiment; independent verifier process."""
import argparse,json,os,subprocess,sys,time
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--library',required=True)
    ap.add_argument('--cache',required=True);ap.add_argument('--statement',required=True)
    ap.add_argument('--terminal-degree',type=int,choices=[1,64],default=1);ap.add_argument('--output-dir',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_global_chain as gc
    from pq384_source_cache import SourceCache
    from pq384_native_fft import NativeFFT
    serial=json.loads(Path(a.statement).read_text());args=serial.copy()
    for key in ('statement','parent_binding','expected_root'):args[key]=bytes.fromhex(args[key])
    started=time.perf_counter()
    with SourceCache(a.cache,**{k:args[k] for k in ('expected_root','log_rows','width','packing')}) as cache:
        proof=gc.prove_cached(cache,NativeFFT(a.library),terminal_degree=a.terminal_degree,**args)
    proving=time.perf_counter()-started
    out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True)
    pp=out/'proof.json';sp=out/'statement.json';pp.write_text(json.dumps(proof,separators=(',',':')));sp.write_text(json.dumps(serial))
    env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir])
    started=time.perf_counter()
    result=subprocess.run([sys.executable,str(Path(gc.__file__)),str(pp),str(sp),str(a.terminal_degree)],
                          check=True,capture_output=True,text=True,env=env)
    report=dict(status='PASS',profile=gc.PROFILE,rows=1<<args['log_rows'],width=args['width'],packing=args['packing'],
        degree=(1<<args['log_rows'])*args['packing'],terminal_degree=a.terminal_degree,
        fold_rounds=len(proof['rounds']),global_queries=gc.QUERIES,prover_seconds=proving,
        separate_verifier_seconds=time.perf_counter()-started,proof_json_bytes=pp.stat().st_size,
        verification=result.stdout.strip(),source_root=args['expected_root'].hex(),
        limits=['Diagnostic Q8/Ext4; no proximity/RBR/QROM theorem inherited',
                'Constant terminal baseline' if a.terminal_degree==1 else 'Terminal64 replacement soundness proof outstanding'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
