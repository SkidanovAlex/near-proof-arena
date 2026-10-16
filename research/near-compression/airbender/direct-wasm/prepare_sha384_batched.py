"""Project honest 80-round prefixes; verify the externally derived public tape.

This new diagnostic profile does not authenticate arbitrary recursive input
routing. Extra public setup elements are reported explicitly.
"""
import argparse,hashlib,json
from pathlib import Path
P=2013265921
IV=[0xcbbb9d5dc1059ed8,0x629a292a367cd507,0x9159015a3070dd17,0x152fecd8f70e5939,0x67332667ffc00b31,0x8eb44a8768581511,0xdb0c2e0d64f98fa7,0x47b5481dbefa4fa4]
def public_tape(message):
    padded=message+b'\x80'+bytes((111-len(message))%128)+(8*len(message)).to_bytes(16,'big')
    count=len(padded)//128
    words=[int.from_bytes(padded[i:i+8],'big') for i in range(0,len(padded),8)]
    limbs=lambda ws:[(w>>(16*j))&65535 for w in ws for j in range(4)]
    return list(message+hashlib.sha384(message).digest())+[1,0,0,0]+limbs(words)+list(count.to_bytes(4,'little'))+limbs(IV)+[1,0,0,0]
def metadata(tag,active,count):
    diff=(tag-count+1)%P;last=int(diff==0)
    return [tag,active,last,0 if last else pow(diff,P-2,P)]
def main():
    p=argparse.ArgumentParser();p.add_argument('--original-directory',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--message',required=True);a=p.parse_args()
    src=Path(a.original_directory);out=Path(a.output_directory);message=Path(a.message).read_bytes();spec=json.loads((out/'spec.json').read_text());original=json.loads((src/'spec.json').read_text());count=len(original['air']['tables']);assert len(spec['air']['tables'])==2
    assert spec['public']==public_tape(message);assert original['public']==list(message+hashlib.sha384(message).digest());assert count==(len(message)+16)//128+1
    rows=[];endpoints=[];hashes=[]
    for tag in range(count):
        f=src/f'source-{tag:02d}-rows.json';raw=f.read_bytes();hashes.append(hashlib.sha256(raw).hexdigest());old=json.loads(raw)['rows'];assert len(old)==128 and all(len(r)==6944 for r in old)
        for phase,row in enumerate(old[:80]):
            assert row[5152:5280]==[int(j==phase) for j in range(128)]
            rows.append(row[:5232]+[1,tag])
        endpoints.append(old[79][5280:]+metadata(tag,1,count))
    while len(rows)<1<<spec['log_rows'][0]:rows.append([0]*5234)
    while len(endpoints)<1<<spec['log_rows'][1]:endpoints.append([0]*1664+metadata(0,0,count))
    assert len(rows)==1<<spec['log_rows'][0] and len(endpoints)==1<<spec['log_rows'][1]
    for i,r in enumerate([rows,endpoints]):(out/f'source-{i:02d}-rows.json').write_text(json.dumps({'rows':r},separators=(',',':')))
    report={'scope':'Diagnostic derived-public profile; full reset/routing semantic refinement pending','status':'PASS','source_sha256':hashes,'message_sha256':hashlib.sha256(message).hexdigest(),'blocks':count,'active_core_rows':80*count,'core_rows':len(rows),'endpoint_rows':len(endpoints),'old_endpoint_cells':count*128*5280+len(endpoints)*1668,'new_cells':len(rows)*5234+len(endpoints)*1668,'public_field_elements':len(spec['public']),'additional_public_elements':64*count+40,'additional_public_fixed_width_bytes':4*(64*count+40),'packing_effects':[]}
    for n in [4,5,6,8,12,16,24,32]:
        height=1<<(80*n-1).bit_length();ep=1<<max(1,(n-1).bit_length());old=n*128*5280+ep*1668;new=height*5234+ep*1668
        report['packing_effects'].append({'blocks':n,'active_rows':80*n,'core_rows':height,'old_cells':old,'new_cells':new,'saving_percent':100*(1-new/old),'additional_public_bytes':4*(64*n+40)})
    (out/'preparation-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
