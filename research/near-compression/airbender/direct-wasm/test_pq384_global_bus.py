"""Fresh auxiliary/global-only failure, emptyaux policy and authenticated codecs."""
import argparse,copy,json,os,struct,subprocess,sys,tempfile,time
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--small-directory',required=True)
    ap.add_argument('--full-directory',required=True);ap.add_argument('--output-dir',required=True)
    ap.add_argument('--rs-binary',required=True);ap.add_argument('--folded-library',required=True);ap.add_argument('--fft-library',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_global_bus as bus
    import pq384_global_bus_codec as codec
    out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True);env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir])
    negatives=0;shared_negatives=0;reports=[]
    for name,directory in [('small',a.small_directory),('full',a.full_directory)]:
        directory=Path(directory);proof=json.loads((directory/'proof.json').read_text());trusted=json.loads((directory/'statement.json').read_text())
        spec=trusted['spec'];roots=[bytes.fromhex(v) for v in trusted['roots']]
        started=time.perf_counter();encoded=codec.encode(proof,spec,roots);assert codec.decode(encoded,spec,roots)==proof
        assert codec.verify_shared(encoded,spec,roots)
        path=out/(name+'.bin');path.write_bytes(encoded)
        checked=subprocess.run([sys.executable,str(Path(codec.__file__)),str(path),str(directory/'statement.json')],env=env,check=True,capture_output=True,text=True)
        def reject(data,s=spec,rs=roots):
            nonlocal negatives,shared_negatives
            try:codec.decode(data,s,rs)
            except (ValueError,TypeError,IndexError,KeyError):negatives+=1
            else:raise AssertionError('bad binary accepted')
            try:codec.verify_shared(data,s,rs)
            except (ValueError,TypeError,IndexError,KeyError):shared_negatives+=1
            else:raise AssertionError('shared verifier accepted bad binary')
        for bad in [encoded[:-1],encoded+b'\0',b'X'+encoded[1:],bytes(codec.max_size(spec)+1)]:reject(bad)
        for offset in [len(codec.MAGIC),len(codec.MAGIC)+48,len(encoded)//2,len(encoded)-1]:
            bad=bytearray(encoded);bad[offset]^=1;reject(bytes(bad))
        bad=bytearray(encoded);bad[len(codec.MAGIC)+48*len(roots)+48:len(codec.MAGIC)+48*len(roots)+52]=struct.pack('<I',bus.P);reject(bytes(bad))
        wrong=copy.deepcopy(spec);wrong['public'][0]^=1;reject(encoded,wrong)
        wrongroots=list(roots);wrongroots[0]=bytes([roots[0][0]^1])+roots[0][1:];reject(encoded,spec,wrongroots)
        reports.append(dict(case=name,bytes=len(encoded),transported_source_commitment_bytes=48*len(roots),tables=len(spec['air']['tables']),verification=checked.stdout.strip(),test_seconds=time.perf_counter()-started))
    # Re-run the small producer on independently invalid bus messages. All local
    # proofs/PCS should accept; ONLY the final product check must reject.
    reference=Path(a.reference_dir);results=reference.parent.parent/'results';runner=Path(__file__).with_name('run_pq384_global_bus.py')
    def produce(specpath,pattern,target):
        return subprocess.run([sys.executable,str(runner),'--reference-dir',a.reference_dir,'--spec',str(specpath),
            '--source-directory',str(results),'--source-pattern',pattern,'--rs-binary',a.rs_binary,
            '--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(target)],env=env,capture_output=True,text=True)
    work=Path(tempfile.mkdtemp(prefix='near-globalbus-negative-'))
    invalid=work/'invalid';run=produce(results/'scheduled-bus-spec.json','scheduled-bus-invalid-source-{index}.json',invalid)
    assert run.returncode!=0 and (invalid/'proof.json').exists()
    p=json.loads((invalid/'proof.json').read_text());s=json.loads((invalid/'statement.json').read_text());rs=[bytes.fromhex(v) for v in s['roots']]
    alpha,gamma=bus.verify_local(p,s['spec'],rs);assert not bus.global_fingerprint_balance(s['spec'],p['finals'],alpha,gamma)
    try:bus.verify(p,s['spec'],rs)
    except ValueError:negatives+=1
    else:raise AssertionError('global-only violation accepted')
    # No interactions, no public messages: verifier-derived zero auxiliary width.
    empty=json.loads((results/'scheduled-bus-spec.json').read_text());empty['air']['pubSegs']=[]
    for table in empty['air']['tables']:table['interactions']=[]
    ep=work/'empty-spec.json';ep.write_text(json.dumps(empty));emptyout=work/'empty'
    run=produce(ep,'scheduled-bus-source-{index}.json',emptyout);assert run.returncode==0,run.stderr
    p=json.loads((emptyout/'proof.json').read_text());s=json.loads((emptyout/'statement.json').read_text());rs=[bytes.fromhex(v) for v in s['roots']]
    assert s['spec']['aux_packings']==[0,0] and all(len(part['openings'])==1 for part in p['tables'])
    b=codec.encode(p,s['spec'],rs);assert codec.decode(b,s['spec'],rs)==p
    assert codec.verify_shared(b,s['spec'],rs)
    bad=copy.deepcopy(p);bad['aux_roots'][0]='00'*48
    try:bus.verify(bad,s['spec'],rs)
    except ValueError:negatives+=1
    else:raise AssertionError('noncanonical empty root accepted')
    report=dict(status='PASS',cases=reports,negative_checks=negatives,global_only_invalid_local_accepts=True,
        global_only_invalid_full_rejects=True,empty_auxiliary_policy_pass=True,extra_artifacts=str(work),
        shared_binary_verification=True,shared_binary_rejections=shared_negatives,
        scope='Complete diagnostic AIR/bus fingerprint checks, not certified exact balance or security')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
