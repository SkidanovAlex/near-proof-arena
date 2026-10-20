"""Replay the actual call compiler's layer placements with the proved Lean checker."""
import argparse,gzip,hashlib,json,subprocess,time
from pathlib import Path
import sha384_call_pcs as cp
import check_terminal_dag_certificates as routes


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    fixture=package/'results/call-array-parity/circuits.json.gz'
    cases=[c for c in json.loads(gzip.decompress(fixture.read_bytes())) if c['expected']]
    reports=[];captures=[]
    for i,case in enumerate(cases):
        coeff=[tuple(c) for c in case['coefficients']];claim=tuple(case['claim'])
        circuit=cp.compile_dag(coeff,claim,case['capacity'])
        assert circuit['nodes']==case['nodes'] and circuit['root']==case['root'],'DAG changed since call certificate'
        layout=cp.g.layer_circuit(circuit);certificate=routes.generate(circuit,layout)
        counts=routes.validate(circuit,layout,certificate)
        capture=out/f'case-{i}.json';capture.write_text(json.dumps(dict(circuit=circuit,layout=layout,certificate=certificate),separators=(',',':')))
        captures.append(capture)
        start=time.monotonic()
        run=subprocess.run(['lake','env','lean','--run','CheckStoredRoutes.lean',str(capture)],cwd=package,text=True,capture_output=True,timeout=120)
        (out/f'case-{i}.log').write_text(run.stdout+run.stderr);run.check_returncode()
        result=json.loads(run.stdout);assert result['status']=='PASS'
        assert result['nodes']==len(circuit['nodes']) and result['layers']==len(layout['layers'])
        reports.append(dict(case=i,capacity=case['capacity'],result=result,route_counts=counts,
            seconds=time.monotonic()-start,sha256=hashlib.sha256(capture.read_bytes()).hexdigest()))
    # Reuse established negative cases against the real nonempty call layout.
    negative=out/'negative-report.json'
    run=subprocess.run(['python3','airbender/direct-wasm/test_lean_stored_routes.py','--capture',str(captures[0]),'--output',str(negative)],cwd=package,text=True,capture_output=True,timeout=240)
    (out/'negative.log').write_text(run.stdout+run.stderr);run.check_returncode()
    mutations=json.loads(negative.read_text())['captures'][0]['rejected'];assert len(mutations)==9
    report=dict(status='PASS',captures=reports,negative_cases=mutations,
        source_fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest(),
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in
            [Path(__file__),Path(cp.__file__),package/'CheckStoredRoutes.lean',package/'NearCompression/CallCircuitCheck.lean',package/'airbender/direct-wasm/check_terminal_dag_certificates.py']},
        scope='Exact call DAGs from prior checked fixtures are lowered by the actual compiler and accepted by the proved Lean layer checker. The existing composition theorem identifies the layered root with dot-minus-claim for all private inputs. Runtime checker execution is not kernel reduction of these JSON fixtures; parser refinement, transcript/PCS/QROM composition and full recursion remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASS',captures=len(reports),negative_cases=len(mutations))))

if __name__=='__main__':main()
