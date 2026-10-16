"""Execute typed Lean reconstruction checks; diagnostic inputs, not extraction."""
import argparse,copy,hashlib,json,subprocess,tempfile,time,sys
sys.setrecursionlimit(10000)
from pathlib import Path

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(bundle,rebuild,manifest,air,seed,ok):
    start=time.perf_counter()
    p=subprocess.run(['lake','env','lean','--run','CheckRebuildRecords.lean',str(bundle),str(rebuild),str(manifest),str(air),str(seed)],capture_output=True,text=True,timeout=180)
    output=p.stdout+p.stderr
    if ok:
        if p.returncode:raise RuntimeError(output)
        value=json.loads(p.stdout.strip().splitlines()[-1]);assert value['status']=='PASS'
        return dict(result=value,seconds=time.perf_counter()-start)
    if not p.returncode or 'uncaught exception:' not in output or 'error:' in output:raise RuntimeError('Not a runtime rejection: '+output)
    return output.strip().splitlines()[-1]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--bundle',type=Path,required=True);ap.add_argument('--rebuild',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--manifest',type=Path,required=True);ap.add_argument('--air',type=Path,required=True);a=ap.parse_args()
    stored=subprocess.run(['lake','env','lean','--run','CheckStoredRoutes.lean',str(a.bundle)],capture_output=True,text=True,timeout=180)
    if stored.returncode:raise RuntimeError(stored.stdout+stored.stderr)
    stored_result=json.loads(stored.stdout.strip().splitlines()[-1]);assert stored_result['status']=='PASS'
    original=json.loads(a.rebuild.read_text());positive=[run(a.bundle,a.rebuild,a.manifest,a.air,seed,True) for seed in (0,7)]
    p=original['programs'][0]
    expansion=next(k for k,r in p['records'].items() if 'tree' in r)
    inp=next(k for k in p['records'] if p['instructions'][int(k)][0] in (1,2))
    mutations=[('wrong-root',lambda x:x['programs'][0].__setitem__('root',0)),
      ('wrong-expansion-sign',lambda x:x['programs'][0]['records'][expansion]['tree'].__setitem__(2,False)),
      ('missing-root-record',lambda x:x['programs'][0]['records'].pop(str(len(p['instructions'])-1))),
      ('changed-input-target',lambda x:x['programs'][0]['records'][inp].__setitem__('node',0)),
      ('changed-selector',lambda x:x['programs'][0]['selectors']['first'].__setitem__(0,(p['selectors']['first'][0]+1)%2013265921)),
      ('unknown-opcode',lambda x:x['programs'][0]['instructions'][0].__setitem__(0,99)),
      ('wrong-batch-power',lambda x:x['outputs'][1].__setitem__('power',x['outputs'][0]['power'])),
      ('wrong-batch-weight',lambda x:x['outputs'][0].__setitem__('weight',x['outputs'][0]['claim'])),
      ('wrong-batch-claim',lambda x:x['outputs'][0].__setitem__('claim',x['outputs'][0]['weight'])),
      ('missing-batch-entry',lambda x:x['outputs'].pop()),
      ('wrong-final-root',lambda x:x.__setitem__('root',0))]
    rejected=[]
    with tempfile.TemporaryDirectory() as d:
        for label,mutate in mutations:
            x=copy.deepcopy(original);mutate(x);path=Path(d)/'mutated.json';path.write_text(json.dumps(x))
            rejected.append(dict(case=label,reason=run(a.bundle,path,a.manifest,a.air,0,False)))
        for label,key in [('changed-expected-rho','rho'),('changed-expected-weight','weights'),('changed-expected-claim','claims')]:
            m=json.loads(a.manifest.read_text());value=m['expected_batch'][key]
            if key!='rho':value=value[0]
            value[0]=(value[0]+1)%2013265921
            path=Path(d)/'manifest.json';path.write_text(json.dumps(m))
            rejected.append(dict(case=label,reason=run(a.bundle,a.rebuild,path,a.air,0,False)))
        point_cases=[('changed-terminal-point',lambda x:x['expected_tables'][0]['point'][0].__setitem__(0,(x['expected_tables'][0]['point'][0][0]+1)%2013265921)),
          ('truncated-terminal-point',lambda x:x['expected_tables'][0]['point'].pop()),
          ('wrong-terminal-row-log',lambda x:x['expected_tables'][0].__setitem__('row_log',x['expected_tables'][0]['row_log']+1)),
          ('missing-terminal-table',lambda x:x['expected_tables'].pop())]
        for label,mutate in point_cases:
            value=json.loads(a.manifest.read_text());mutate(value);path=Path(d)/'manifest.json';path.write_text(json.dumps(value))
            reason=run(a.bundle,a.rebuild,path,a.air,0,False)
            assert ('batch count' if label=='missing-terminal-table' else 'terminal selector products rejected') in reason
            rejected.append(dict(case=label,reason=reason))
        air_cases=[('unknown-air-expression',lambda x:x['tables'][0]['expression_routes'][0].__setitem__('expr',['unknown'])),
          ('out-of-range-air-register',lambda x:x['tables'][0]['expression_routes'][0].__setitem__('register',1000000)),
          ('wrong-air-mixing',lambda x:x['tables'][0]['mixing'].__setitem__(0,(x['tables'][0]['mixing'][0]+1)%2013265921)),
          ('wrong-accumulator-coefficient',lambda x:x['tables'][0]['accumulation']['steps'][0].__setitem__('coefficient',x['tables'][0]['accumulation']['zero'])),
          ('wrong-air-final-copy',lambda x:x['tables'][0]['accumulation'].__setitem__('output',0)),
          ('missing-air-table',lambda x:x['tables'].pop()),
          ('wrong-bus-operation',lambda x:x['tables'][0]['bus_formulas'][0]['formula'].__setitem__(0,'add')),
          ('missing-bus-register',lambda x:x['tables'][0]['bus_formulas'][0].__setitem__('register',1000000)),
          ('missing-bus-formula',lambda x:x['tables'][0]['bus_formulas'].pop()),
          ('reordered-bus-formulas',lambda x:x['tables'][0]['bus_formulas'].reverse())]
        for label,mutate in air_cases:
            value=json.loads(a.air.read_text());mutate(value);path=Path(d)/'air.json';path.write_text(json.dumps(value))
            rejected.append(dict(case=label,reason=run(a.bundle,a.rebuild,a.manifest,path,0,False)))
    report=dict(status='PASS',bundle=str(a.bundle),bundle_sha256=sha(a.bundle),rebuild=str(a.rebuild),rebuild_sha256=sha(a.rebuild),adapter_sha256=sha(Path('CheckRebuildRecords.lean')),manifest_sha256=sha(a.manifest),air_sha256=sha(a.air),positive=positive,rejected=rejected,
      stored_bundle_check=stored_result,scope='Native combined finite compiler checker on two diagnostic assignments with supplied replay manifest. Includes selector products against supplied replay terminal points and ordered AIR and bus-formula evaluation checks; excludes formal expected-formula generation, commitment extraction, parser refinement and concrete kernel proof terms.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASS',assignments=len(positive),rejections=len(rejected))))
if __name__=='__main__':main()
