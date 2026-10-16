import argparse,copy,json,sys,tempfile,subprocess,os
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--input-directory',required=True)
    ap.add_argument('--rs-binary',required=True);ap.add_argument('--folded-library',required=True);ap.add_argument('--fft-library',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir);import pq384_seed_gkr_bus as bus
    def verify(p,s,r):return bus.verify(p,s,r,bus.configure(s['air']))
    inp=Path(a.input_directory);proof=json.loads((inp/'proof.json').read_text());trusted=json.loads((inp/'statement.json').read_text());spec=trusted['spec'];roots=[bytes.fromhex(x) for x in trusted['roots']]
    assert verify(proof,spec,roots);neg=0
    def reject(p=proof,s=spec,rs=roots):
        nonlocal neg
        try:verify(p,s,rs)
        except (ValueError,IndexError,KeyError,TypeError):neg+=1
        else:raise AssertionError('accepted mutation')
    for key in ('aux_roots','finals','tables','gkr','opening'):
        bad=copy.deepcopy(proof);del bad[key];reject(bad)
    for key in ('aux_roots','finals','tables'):
        bad=copy.deepcopy(proof);bad[key].pop();reject(bad)
    bad=copy.deepcopy(proof);bad['tables'][0][0][0][0]^=1;reject(bad)
    bad=copy.deepcopy(proof);bad['gkr']['layers'][0]['inputs'][0][0]^=1;reject(bad)
    bad=copy.deepcopy(proof);bad['gkr']['layers'][0]['rounds'][0][0][0]^=1;reject(bad)
    bad=copy.deepcopy(proof);bad['opening']['reduction'][0][0][0]^=1;reject(bad)
    bad=copy.deepcopy(proof);bad['opening']['queries'][0]['sources'][0]['leaf'][0]^=1;reject(bad)
    bad=copy.deepcopy(proof);bad['opening']['queries'][0]['folds'][0]['leaf'][0]^=1;reject(bad)
    bad=copy.deepcopy(proof);bad['opening']['terminal']['coefficients'][0][0][0]^=1;reject(bad)
    bad=copy.deepcopy(spec);bad['public'][0]=(bad['public'][0]+1)%2013265921;reject(s=bad)
    bad=copy.deepcopy(spec);bad['air']['tables'][0]['constraints'].append(['c',1]);reject(s=bad)
    reject(rs=roots[::-1]);bad=copy.deepcopy(proof);bad['opening']['queries'][0]['sources'].reverse();reject(bad)
    work=Path(tempfile.mkdtemp(prefix='near-gkr-bus-negative-'));results=Path(a.reference_dir).parents[1]/'results'
    runner=Path(__file__).with_name('run_pq384_seed_gkr_bus.py');env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir])
    def produce(sp,pattern,out,source=results):
        return subprocess.run([sys.executable,str(runner),'--reference-dir',a.reference_dir,'--spec',str(sp),'--source-directory',str(source),'--source-pattern',pattern,
            '--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(out)],env=env,capture_output=True,text=True)
    invalid=work/'bus-invalid';run=produce(results/'scheduled-bus-spec.json','scheduled-bus-invalid-source-{index}.json',invalid)
    assert run.returncode!=0 and (invalid/'proof.json').exists(),run.stderr
    p=json.loads((invalid/'proof.json').read_text());s=json.loads((invalid/'statement.json').read_text());rs=[bytes.fromhex(v) for v in s['roots']]
    alpha,gamma=bus.verify_local(p,s['spec'],rs,bus.configure(s['spec']['air']));assert not bus.old.global_fingerprint_balance(s['spec'],p['finals'],alpha,gamma);reject(p,s['spec'],rs)
    empty=json.loads((results/'scheduled-bus-spec.json').read_text());empty['air']['pubSegs']=[]
    for table in empty['air']['tables']:table['interactions']=[]
    sp=work/'empty.json';sp.write_text(json.dumps(empty));out=work/'empty';run=produce(sp,'scheduled-bus-source-{index}.json',out);assert run.returncode==0,run.stderr
    p=json.loads((out/'proof.json').read_text());s=json.loads((out/'statement.json').read_text());rs=[bytes.fromhex(v) for v in s['roots']];assert verify(p,s['spec'],rs)
    p['aux_roots'][0]='00'*48;reject(p,s['spec'],rs)
    source=work/'changed-source';source.mkdir()
    for i in range(2):
        data=json.loads((results/f'scheduled-bus-source-{i}.json').read_text())
        if i==0:data['rows'][0][0]=(data['rows'][0][0]+1)%2013265921
        (source/f'source-{i}.json').write_text(json.dumps(data))
    run=produce(results/'scheduled-bus-spec.json','source-{index}.json',work/'invalid-local',source);assert run.returncode!=0 and 'invalid trace constraints' in run.stderr,run.stderr;neg+=1
    for key in ('digest','compiler','air'):
        config=bus.configure(spec['air'])
        if key=='digest':config[key]=bytes(48)
        elif key=='compiler':config[key]=b'wrong-config'
        else:config[key]['numPub']+=1
        try:bus.verify(proof,spec,roots,config)
        except ValueError:neg+=1
        else:raise AssertionError('wrong trusted config accepted')
    report=dict(status='PASS' ,negative_checks=neg,bus_only_invalid_local_accepts=True,bus_only_invalid_full_rejects=True,empty_aux_pass=True,fresh_invalid_trace_rejected=True,artifact_directory=str(work),scope='Executable complete diagnostic; no proven soundness level')
    (work/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))

if __name__=='__main__':main()
