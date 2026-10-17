"""Execution-to-PCS bank mapping and external-profile rejection regressions."""
import argparse,copy,gzip,json
from pathlib import Path
import ext8_commitment_profiles as c
import pq384_ext8_reference as f
import pq384_ext8_weight_families as families


def main():
    p=argparse.ArgumentParser();p.add_argument('--statement',type=Path,required=True);p.add_argument('--opening',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    def read(path):
        raw=path.read_bytes();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
    st=read(a.statement);spec=st['spec'];roots=st['roots'];aux=['ab'*48]*4
    cfg=read(a.opening);logical=[]
    for i,b in enumerate(cfg['branches']):
        logical.append(dict(table=i//2,branch=i%2,**{k:v for k,v in b.items() if k!='root'}))
    bound=c.bind_branches(spec,logical,roots,aux,'phase-pooled-v1');banks=c.plan(spec)
    assert [(b['log_rows'],b['width'],b['packing']) for b in bound]==[(11,7091,128),(11,296,32),(5,179,4)]
    assert [t['offset'] for t in bound[0]['terms']]==[0,5234,6900]
    assert [t['offset'] for t in bound[1]['terms']]==[0,24,48,288]
    for b,bank in zip(bound,banks):
        families.validate_fields(b);families.validate_weights(b)
        if 'terms' not in b:continue
        for term,block in zip(b['terms'],bank['blocks']):
            old=logical[2*block['table']+int(bank['phase']=='auxiliary')]
            assert term['row_point']==old['row_point']
            for side,name in enumerate(('current','next')):
                assert term[name]==[x for lane in old['lanes'] for x in lane[side]][:old['width']]
    assert bound[2]==dict(root=roots[3],**{k:v for k,v in logical[6].items() if k not in ('table','branch')})
    assert c.bind_branches(spec,list(reversed(logical)),roots,aux,'phase-pooled-v1')==bound
    rb=[bytes.fromhex(r) for r in roots]
    assert c.statement(spec,rb,'separate')!=c.statement(spec,rb,'phase-pooled-v1')
    # Independent tiny physical scatter: short tables retain logical height.
    bank=dict(log_rows=2,width=3,blocks=[dict(table=0,log_rows=2,width=1,offset=0),dict(table=1,log_rows=1,width=2,offset=1)])
    assert c.bank_rows(bank,[[[1],[2],[3],[4]],[[5,6],[7,8]]])==[[1,5,6],[2,7,8],[3,0,0],[4,0,0]]
    negatives=[]
    def reject(name,fn):
        try:fn()
        except ValueError:negatives.append(name)
        else:raise AssertionError(name)
    def check(ds):return c.bind_branches(spec,ds,roots,aux,'phase-pooled-v1')
    reject('missing-logical-table',lambda:check(logical[:-1]))
    reject('duplicate-logical-table',lambda:check(logical+[logical[0]]))
    for key,value in [('table',9),('branch',2),('width',5233),('packing',64),('log_rows',10),('offset',1)]:
        bad=copy.deepcopy(logical);bad[0][key]=value
        reject('altered-'+key,lambda:check(bad))
    bad=copy.deepcopy(logical);bad[0]['lanes'][-1][0][-1]=list(f.ONE)
    reject('nonzero-padding-weight',lambda:check(bad))
    bad=copy.deepcopy(logical);bad[0]['row_point']=bad[0]['row_point'][:-1]
    reject('wrong-logical-point-height',lambda:check(bad))
    reject('source-alias',lambda:c.check_roots(spec,[roots[0],roots[3],roots[2],roots[3]],aux,'phase-pooled-v1'))
    reject('auxiliary-alias',lambda:c.check_roots(spec,roots,aux[:3]+['cd'*48],'phase-pooled-v1'))
    reject('unknown-profile',lambda:c.check_roots(spec,roots,profile='proof-selected'))
    badspec=copy.deepcopy(spec);badspec['source_packings'][3]=3
    reject('non-power-two-packing',lambda:c.plan(badspec))
    reject('logical-row-shape',lambda:c.bank_rows(bank,[[[1]],[[5,6],[7,8]]]))
    result=dict(status='PASS',physical_banks=3,logical_branches=8,negative_cases=negatives,canonical_order=True,domain_separation=True,scope='Execution descriptor mapping regression; no cryptographic soundness claim.')
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
