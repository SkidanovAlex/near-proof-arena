"""Exact projection of the existing canonical multiblock compression witness."""
import argparse,hashlib,json
from pathlib import Path
P=2013265921

def metadata(tag,active,count):
    diff=(tag-(count-1))%P;last=int(diff==0)
    return [tag,active,last,0 if last else pow(diff,P-2,P)]

def main():
    p=argparse.ArgumentParser();p.add_argument('--original-directory',required=True);p.add_argument('--output-directory',required=True);a=p.parse_args();inp=Path(a.original_directory);out=Path(a.output_directory);spec=json.loads((out/'spec.json').read_text());original=json.loads((inp/'spec.json').read_text());count=len(original['air']['tables'])
    assert spec['public']==original['public']+[1,0,0,0];assert len(spec['air']['tables'])==count+1
    endpoint=[];hashes=[];original_cells=0;new_cells=0
    for i in range(count):
        path=inp/f'source-{i:02d}-rows.json';raw=path.read_bytes();hashes.append(hashlib.sha256(raw).hexdigest());rows=json.loads(raw)['rows'];assert len(rows)==128 and all(len(r)==6944 for r in rows)
        core=[r[:5280] for r in rows];endpoint.append(rows[79][5280:]+metadata(i,1,count));original_cells+=128*6944;new_cells+=128*5280
        (out/f'source-{i:02d}-rows.json').write_text(json.dumps({'rows':core},separators=(',',':')))
    while len(endpoint)<2**spec['log_rows'][-1]:endpoint.append([0]*1664+metadata(0,0,count))
    new_cells+=len(endpoint)*1668;(out/f'source-{count:02d}-rows.json').write_text(json.dumps({'rows':endpoint},separators=(',',':')))
    report=dict(status='PASS',original_source_sha256=hashes,core_prefix_cells_exact=count*128*5280,endpoint_adder_cells_exact=count*1664,
        old_cells=original_cells,new_cells=new_cells,reduction_percent=100*(1-new_cells/original_cells),endpoint_rows=len(endpoint),
        public_original_prefix_unchanged=True,derived_public_count_bytes=[1,0,0,0],scope='Witness projection only; newAIRfullproof and routing checks required')
    (out/'preparation-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
