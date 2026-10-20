"""Complete verifier replay of retained prepared execution; no source rows."""
import argparse,copy,hashlib,json,subprocess,sys
from pathlib import Path
import verify_ext8_execution as v


def main():
    p=argparse.ArgumentParser();p.add_argument('--capture',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    read=lambda name:json.loads((a.capture/name).read_text())
    reduction=read('reduction.json');cfg=read('opening.json');wire=(a.capture/'proof.bin').read_bytes()
    package=Path(__file__).resolve().parents[2]
    statement_path=package/'results/pq384-literal193-gkr-fixed13/statement.json'
    statement=json.loads(statement_path.read_text());spec,roots=statement['spec'],statement['roots'];q=cfg['queries']
    params=v.opening_parameters(reduction,spec,roots)
    expected=(bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim'])
    # Compare serialization so tuples/lists cannot obscure a mismatch.
    assert params[:2]==expected[:2] and json.dumps(params[2:],sort_keys=True)==json.dumps(expected[2:],sort_keys=True)
    assert v.verify(reduction,wire,spec,roots,queries=q)
    negative=[]
    def reject(name,r=reduction,w=wire,s=spec,rs=roots,queries=q):
        try:v.verify(r,w,s,rs,queries=queries)
        except (ValueError,KeyError):negative.append(name)
        else:raise AssertionError(name)
    bad=copy.deepcopy(reduction);bad['finals'][0][0][0]=(bad['finals'][0][0][0]+1)%v.f.P;reject('bus-final',r=bad)
    bad=copy.deepcopy(reduction);bad['aux_roots'][0]='00'*48;reject('aux-root',r=bad)
    bad=copy.deepcopy(reduction);bad['local'][0][0][0][0]=(bad['local'][0][0][0][0]+1)%v.f.P;reject('local-round',r=bad)
    bad=copy.deepcopy(reduction);bad['gkr']['layers'][0]['inputs'][0][0]=(bad['gkr']['layers'][0]['inputs'][0][0]+1)%v.f.P;reject('gkr-input',r=bad)
    bad=copy.deepcopy(reduction);bad['local'].pop();reject('table-count',r=bad)
    bad=copy.deepcopy(reduction);bad['finals'][0].append([0]*8);reject('final-count',r=bad)
    bad=copy.deepcopy(reduction);bad['claim']=[0]*8;reject('prover-selected-claim',r=bad)
    reject('external-root',rs=['00'*48]+roots[1:])
    bad=copy.deepcopy(spec);bad['source_packings'][0]*=2;reject('external-spec',s=bad)
    reject('opening-authentication',w=wire[:-1]+bytes([wire[-1]^1]))
    reject('query-budget',queries=q+1)
    cmd=[sys.executable,str(Path(v.__file__)),'--reduction',str(a.capture/'reduction.json'),'--opening',str(a.capture/'proof.bin'),'--statement',str(statement_path),'--queries',str(q)]
    fresh=subprocess.run(cmd,text=True,capture_output=True);fresh.check_returncode()
    report=dict(status='PASS',queries=q,derived_parameters_match_retained=True,fresh_verifier=fresh.stdout.strip(),negative_cases=negative,opening_bytes=len(wire),source_rows_supplied=False,files={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in (Path(v.__file__),Path(__file__),a.capture/'reduction.json',a.capture/'proof.bin',statement_path)},scope='Full executable reduction replay on retained prepared Wasm, with externally fixed spec/roots and derived PCS weights/claim. Not an all-Ext8 SHA384 compression measurement or formal implementation/QROM certificate.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
