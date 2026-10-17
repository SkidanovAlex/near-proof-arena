"""Derive native continuation input from verified GKR, without column values.

Trace shapes/layouts are trusted metadata exported from the native VK/proof.
The native replay checks their actual commitment/layout context separately.
"""
import hashlib,json,struct
from pathlib import Path
import pq384_terminal_gkr as g
from verify_swirl_prefix_dag import main as verify
from prove_swirl_prefix_dag import BASE,PREFIX
OUT=BASE/'prefix-continuation'


def main(proof=None, c=None, prefix_log=None, shapes=None, layouts=None, write_outputs=True):
    residual,description,proof=verify(proof,c,prefix_log,check_fixture=write_outputs,write_report=write_outputs)
    if c is None:c=json.loads((PREFIX/'controls.json').read_text())
    if shapes is None:shapes=json.loads((OUT/'trace-shapes.json').read_text())
    if layouts is None:layouts=json.loads((BASE/'committed-witness/layouts.json').read_text())
    assert [s['air'] for s in shapes]==[t['air'] for t in c['traces']]
    by_air={s['air']:s for s in shapes};weights={}
    for item in residual['coordinates']:
        tag,kind,part,rotation,column,air=item['coordinate'];shape=by_air[air]
        assert tag=='variable' and kind in (0,1) and rotation in (0,1)
        assert rotation==0 or shape['need_rot']
        if kind==0:
            assert shape['has_preprocessed'];opening_part=1
        else:
            assert 0<=part<=shape['cached_count']
            opening_part=0 if part==shape['cached_count'] else 1+int(shape['has_preprocessed'])+part
        key=(air,opening_part,column)
        pair=weights.setdefault(key,[g.ZERO,g.ZERO]);pair[rotation]=g.add(pair[rotation],tuple(item['weight']))
    lookup={};commit=1
    for t,s in enumerate(shapes):
        lookup[0,t]=(s['air'],0)
        assert s['part_count']==1+int(s['has_preprocessed'])+s['cached_count']
        for part in range(1,s['part_count']):lookup[commit,0]=(s['air'],part);commit+=1
    assert commit==len(layouts)
    ordered=[];used=set()
    for com,l in enumerate(layouts):
        for matrix,column,*_ in l['slices']:
            air,part=lookup[com,matrix];key=air,part,column
            assert key not in used;used.add(key);ordered.extend(weights.get(key,[g.ZERO,g.ZERO]))
    assert weights.keys()<=used
    words=[c['l_skip'],layouts[0]['height'].bit_length()-1-c['l_skip'],len(c['r'])]
    words += [v for x in c['r'] for v in x]+list(residual['claim'])+[len(ordered)//2]
    words += [v for x in ordered for v in x]
    data=struct.pack('<'+'I'*len(words),*words)
    # Canonical JSON boundary binds the preceding public statement and ALL GKR messages.
    binding=hashlib.sha384(json.dumps(dict(profile='nearproof-prefix-gkr-to-whir-v1',
        statement=description,gkr_proof=proof),sort_keys=True,separators=(',',':')).encode()).digest()
    if write_outputs:
        (OUT/'weighted-input.bin').write_bytes(data);(OUT/'gkr-binding.bin').write_bytes(binding)
    Path('/tmp/nearproof-reconstructed-witness/weighted-input.bin').write_bytes(data)
    Path('/tmp/nearproof-prefix-gkr-binding.bin').write_bytes(binding)
    report=dict(status='CONTINUATION_DERIVED_FROM_VERIFIED_PUBLIC_GKR',column_pairs=len(weights),
        native_pairs=len(ordered)//2,zero_filled_columns=len(used-weights.keys()),
        weighted_input_sha256=hashlib.sha256(data).hexdigest(),gkr_binding_hex=binding.hex(),
        scope='Public prefix and GKR verifier derive all weights and binding; no source opening values or matrices read.')
    if write_outputs:
        (OUT/'preparation.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
    return report


if __name__=='__main__':main()
