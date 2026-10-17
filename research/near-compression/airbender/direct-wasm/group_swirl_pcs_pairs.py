"""Group verified fixture GKR residual into current/rotated column weights.

Rechecks against disclosed openings; does not authenticate a replacement PCS.
"""
import gzip,hashlib,json
from pathlib import Path
import pq384_terminal_gkr as g

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/weighted-stack-kernel'


def main(source=ROOT/'results/swirl-security-review/native-dag-gkr', output_dir=OUT):
    paths=[source/'pcs-obligation.json.gz',source/'openings.json.gz']
    obligation,openings=[json.loads(gzip.decompress(p.read_bytes())) for p in paths]
    by_air={r['air']:r for r in openings};pairs={}
    for item in obligation['coordinates']:
        tag,kind,part,rotation,column,air=item['coordinate']
        assert tag=='variable' and kind in (0,1) and rotation in (0,1)
        key=(air,kind,part,column)
        if key not in pairs:pairs[key]=[g.ZERO,g.ZERO]
        pairs[key][rotation]=g.add(pairs[key][rotation],tuple(item['weight']))
    total=g.ZERO;rows=[]
    for (air,kind,part,column),(a,b) in sorted(pairs.items()):
        r=by_air[air]
        if kind==0:assert r['has_preprocessed'];commit_part=1
        else:
            assert part<=r['cached_count']
            commit_part=0 if part==r['cached_count'] else 1+int(r['has_preprocessed'])+part
        stride=2 if r['need_rot'] else 1
        current=tuple(r['parts'][commit_part][stride*column])
        if r['need_rot']:nxt=tuple(r['parts'][commit_part][stride*column+1])
        else:assert b==g.ZERO;nxt=g.ZERO
        total=g.add(total,g.add(g.mul(a,current),g.mul(b,nxt)))
        rows.append(dict(air=air,kind=kind,dag_part=part,opening_part=commit_part,column=column,current_weight=a,rotated_weight=b))
    assert total==tuple(obligation['claim'])
    output_dir.mkdir(parents=True,exist_ok=True)
    result=dict(status='NATIVE_RESIDUAL_COLUMN_PAIRS_CHECKED',source_coordinates=len(obligation['coordinates']),
        column_pairs=len(rows),nonzero_rotation_pairs=sum(r['rotated_weight']!=g.ZERO for r in rows),
        claim=total,pairs=rows,
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        scope='Column pairing only; committed stacked-layout placement and new PCS proof remain required.')
    (output_dir/'native-pairs.json.gz').write_bytes(gzip.compress(json.dumps(result).encode(),mtime=0))
    print({k:v for k,v in result.items() if k not in ('pairs','sha256')})


if __name__=='__main__':main()
