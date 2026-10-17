"""Encode fixed native layouts and the new GKR residual for the Rust probe."""
import gzip,json,struct
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]/'results/swirl-security-review'

def main():
    c=json.loads(gzip.decompress((ROOT/'committed-witness/point-capture.jsonl.gz').read_bytes()))
    layouts=json.loads((ROOT/'committed-witness/layouts.json').read_text())
    openings=json.loads(gzip.decompress((ROOT/'committed-witness/openings.json.gz').read_bytes()))
    pairs=json.loads(gzip.decompress((ROOT/'witness-dag-gkr/native-pairs.json.gz').read_bytes()))
    lookup={};commit=1
    for t,o in enumerate(openings):
        lookup[0,t]=(o['air'],0)
        for part in range(1,len(o['parts'])):
            lookup[commit,0]=(o['air'],part);commit+=1
    weights={(p['air'],p['opening_part'],p['column']):[p['current_weight'],p['rotated_weight']] for p in pairs['pairs']}
    ordered=[];used=set()
    for com,l in enumerate(layouts):
        for matrix,column,*_ in l['slices']:
            air,part=lookup[com,matrix];key=(air,part,column)
            ordered.extend(weights.get(key,[[0]*4,[0]*4]));used.add(key)
    assert weights.keys()<=used
    words=[c['l_skip'],layouts[0]['height'].bit_length()-1-c['l_skip'],len(c['r'])]
    words += [v for x in c['r'] for v in x]+pairs['claim']+[len(ordered)//2]
    words += [v for x in ordered for v in x]
    path=Path('/tmp/nearproof-reconstructed-witness/weighted-input.bin')
    path.write_bytes(struct.pack('<'+'I'*len(words),*words))
    print({'pairs':len(ordered)//2,'zero_filled_columns':len(used-weights.keys()),'bytes':path.stat().st_size})

if __name__=='__main__':main()
