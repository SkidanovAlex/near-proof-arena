"""Actual Ext8 compiler routes checked in Lean; no DAG/authentication claim."""
import argparse, copy, hashlib, json, random, subprocess, sys, tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'generic-air'))
import pq384_ext8_reference as f
import pq384_global_bus as bus
import check_bus_program_formulas as formulas
from pq384_ext8_terminal_compile import compile_weighted

def run(path,positive):
    p=subprocess.run(['lake','env','lean','--run','CheckExt8BusFormulas.lean','--fingerprints',str(path)],capture_output=True,text=True,timeout=90)
    text=p.stdout+p.stderr
    if positive:
        if p.returncode:raise RuntimeError(text)
        result=json.loads(p.stdout.strip().splitlines()[-1]);assert result['status']=='PASS'
        return result
    if not p.returncode or 'uncaught exception:' not in text or 'error:' in text:raise RuntimeError('Expected runtime rejection: '+text)
    return text.strip().splitlines()[-1]

def capture(spec):
    rng=random.Random(108903)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    def normalize(value):
        if isinstance(value,dict):return {k:normalize(v) for k,v in value.items()}
        if isinstance(value,list):
            if len(value)==3 and value[0]=="v":return ["v",value[1],bool(value[2])]
            return [normalize(v) for v in value]
        return value
    spec=normalize(spec)
    cases=[]
    for alpha in (f.ZERO,f.ONE,scalar()):
        for table in spec['air']['tables']:
            words=compile_weighted(table,spec['public'],alpha,scalar(),[scalar() for _ in table['interactions']],scalar(),bus)
            rows=[words[i:i+11] for i in range(0,len(words),11)]
            indices={tuple(row):i for i,row in enumerate(rows)}
            def root(e):
                op=e[0]
                if op=='lit':row=(0,0,0,*e[1])
                elif op in ('current','next'):row=(1 if op=='current' else 2,e[1],0,*f.ZERO)
                elif op in ('first','last','trans'):row=({'first':3,'last':4,'trans':5}[op],0,0,*f.ZERO)
                else:row=({'add':6,'sub':7,'mul':8}[op],root(e[1]),root(e[2]),*f.ZERO)
                return indices[row]
            roots=[]
            for interaction in table['interactions']:
                expr=formulas.lit(f.ZERO);weight=f.ONE
                for message in interaction['msg']:
                    expr=('add',expr,('mul',formulas.expr(message,spec['public'],field=f),formulas.lit(weight)))
                    weight=f.mul(weight,alpha)
                expr=('add',expr,formulas.lit(f.mul(f.base(interaction['bus']+1),weight)))
                roots.append(root(expr))
            cases.append(dict(table=table,public=spec['public'],alpha=alpha,instructions=rows,roots=roots))
    return cases

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    source=Path('results/pq384-literal193-gkr-fixed13/statement.json')
    original=json.loads(json.dumps(capture(json.loads(source.read_text())['spec'])))
    def target(x):return x[-1]
    def wrong_literal(x):
        item=target(x);row=item['instructions'][item['instructions'][item['roots'][0]][2]]
        assert row[0]==0;row[3]=(row[3]+1)%f.P
    mutations=[
        ('changed-alpha',lambda x:target(x)['alpha'].__setitem__(0,(target(x)['alpha'][0]+1)%f.P)),
        ('changed-bus',lambda x:target(x)['table']['interactions'][0].__setitem__('bus',999)),
        ('wrong-root',lambda x:target(x)['roots'].__setitem__(0,len(target(x)['instructions']))),
        ('wrong-live-constant',wrong_literal),
        ('changed-message',lambda x:target(x)['table']['interactions'][0]['msg'].__setitem__(0,['c',123456])),
        ('cyclic-root',lambda x:target(x)['instructions'][target(x)['roots'][0]].__setitem__(1,target(x)['roots'][0])),
        ('zero-column-width',lambda x:target(x)['table'].__setitem__('width',0)),
        ('omitted-root',lambda x:target(x)['roots'].pop()),
        ('empty-capture',lambda x:x.clear())]
    with tempfile.TemporaryDirectory(prefix='expanded-fingerprint-') as tmp:
        path=Path(tmp)/'capture.json';path.write_text(json.dumps(original))
        digest=hashlib.sha256(path.read_bytes()).hexdigest();positive=run(path,True);rejected=[]
        for name,mutate in mutations:
            bad=copy.deepcopy(original);mutate(bad);path.write_text(json.dumps(bad))
            rejected.append(dict(case=name,reason=run(path,False)))
    report=dict(status='PASS',positive=positive,rejections=rejected,capture_sha256=digest,
        statement_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        checker_sha256=hashlib.sha256(Path('CheckExt8BusFormulas.lean').read_bytes()).hexdigest(),
        scope='Actual emitted Ext8 weighted programs; Lean reconstructs message expressions and tags from supplied AIR and checks fingerprint routes. Covers zero/unit/random alpha. No optimized DAG refinement, authenticated AIR/challenges, native Ext8 proof, or security certification.')
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(positive))
if __name__=='__main__':main()
