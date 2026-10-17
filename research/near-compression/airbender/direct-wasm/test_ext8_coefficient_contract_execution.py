"""Check separable coefficient contraction on every actual execution branch.
Replays local/GKR verification from externally fixed spec/roots, regenerates
auxiliaries, then independently converts source and auxiliary coefficients.
This is witness-side validation, not a replacement for PCS verification.
"""
import argparse,gzip,hashlib,json,time
from pathlib import Path
import verify_ext8_execution as v
import ext8_coefficient_claim_contract as contracted


def main():
    p=argparse.ArgumentParser()
    for key in ('capture','statement','source-directory','source-report','output'):
        p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--terminal-profile',choices=v.profiles.PROFILES,default='baseline')
    a=p.parse_args();start=time.perf_counter()
    statement=json.loads(a.statement.read_text());reduction=json.loads((a.capture/'reduction.json').read_text())
    raw=a.source_report.read_bytes();report=json.loads(gzip.decompress(raw) if a.source_report.suffix=='.gz' else raw)
    spec=statement['spec'];expected=report['source_sha256'];rows=[]
    assert len(expected)==len(spec['air']['tables'])
    for i,digest in enumerate(expected):
        raw=(a.source_directory/f'source-{i:02d}-rows.json').read_bytes()
        assert hashlib.sha256(raw).hexdigest()==digest
        rows.append(json.loads(raw)['rows'])
    prefix=v.reduction_prefix(reduction,spec,statement['roots'],terminal_profile=a.terminal_profile)
    st,t,terminals,circuit,layout=prefix
    ob=v.gkr.verify(layout,t.seed,reduction['gkr'],v.f.ZERO)
    transcript=v.Transcript(st);alpha,gamma=v.local.draw(transcript,2)
    generated=[v.aux.generate(table,data,spec['public'],alpha,gamma) for table,data in zip(spec['air']['tables'],rows)]
    assert [x['finals'] for x in generated]==[[tuple(y) for y in fs] for fs in reduction['finals']]
    coordinates=[[[c for value in row for c in value] for row in x['aux_rows']] for x in generated]
    branches=v.opening_branches(spec,terminals,circuit,ob['private_weights'])
    total=v.f.ZERO;checks=[];contraction_start=time.perf_counter()
    for b in branches:
        before=time.perf_counter();data=(rows if b['branch']==0 else coordinates)[b['table']]
        total=v.f.add(total,contracted.coefficient_claim(data,b))
        checks.append(dict(table=b['table'],branch=b['branch'],width=b['width'],rows=len(data),seconds=time.perf_counter()-before))
    assert total==ob['private_claim']
    output=dict(status='PASS',terminal_profile=a.terminal_profile,branches=checks,source_sha256=expected,
                contraction_seconds=time.perf_counter()-contraction_start,total_seconds=time.perf_counter()-start,
                reduction_sha256=hashlib.sha256((a.capture/'reduction.json').read_bytes()).hexdigest(),
                scope='All actual source/auxiliary coefficient claims sum to independently verified GKR input claim. Witness-side check only; no replacement for authenticated PCS.')
    a.output.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))

if __name__=='__main__':main()
