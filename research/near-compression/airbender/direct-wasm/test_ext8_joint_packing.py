"""Exhaustive small packing search and full-size selected-geometry replay."""
import argparse,json,random
from itertools import product
from pathlib import Path
from screen_ext8_joint_packing import optimize
from screen_ext8_grouped_geometry import geometry


def branch(n,w,p,index):return dict(root=str(index),log_rows=n,width=w,packing=p,lanes=[None]*((w+p-1)//p))


def main():
    p=argparse.ArgumentParser();p.add_argument('--report',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();checks=0
    for shapes in ([(2,3),(1,2),(1,3)],[(1,1),(1,3)]):
        use=len(shapes)-1
        for B in (4,16):
            for large,small in [([0,1,1,7],[1,2,3]),([3,6,8],[0,0,1])]:
                answer=optimize(shapes,use,B.bit_length()-1,large,small,max_domain_log=8);allcost=[]
                for ps in product(*[[1<<p for p in range((w-1).bit_length()+1)] for _,w in shapes]):
                    bs=[branch(n,w,p,j) for j,((n,w),p) in enumerate(zip(shapes,ps))];D=max((1<<b['log_rows'])*b['packing'] for b in bs)
                    if B*D>1<<8:continue
                    cd=(1<<shapes[use][0])*ps[use]
                    for k in range(1,min(4,D.bit_length()-1)+1):
                        ck=max(1,k-(D.bit_length()-cd.bit_length()))
                        if ck>min(4,cd.bit_length()-1):continue
                        x=geometry(bs,D,B,large,grouped=True,merkle_layout='coset',first_group=k)
                        y=geometry([bs[use],bs[use]],cd,B,small,grouped=True,merkle_layout='coset',first_group=ck)
                        allcost.append(x['bytes']+y['bytes'])
                assert answer['opening_bytes']==min(allcost);checks+=1
    report=json.loads(a.report.read_text());full=0
    for row in report['records']:
        for run in row['runs']:
            q=row['queries'];rng=random.Random(902000+run['seed']);large=[rng.randrange(1<<27) for _ in range(q)];small=[rng.randrange(1<<27) for _ in range(q)]
            bs=[branch(n,w,x['packing'],j) for j,((n,w),x) in enumerate(zip(report['shapes'],run['branches']))]
            use=report['use_branch'];D=run['degree'];cd=1<<run['branches'][use]['log_degree'];B=row['blowup']
            assert D==max((1<<b['log_rows'])*b['packing'] for b in bs) and B*D<=1<<27
            ck=max(1,run['compression_groups'][0]-(D.bit_length()-cd.bit_length()))
            assert ck==run['call_groups'][0]==run['shared_use_layout']['leaf_bits']
            x=geometry(bs,D,B,large,grouped=True,merkle_layout='coset',first_group=run['compression_groups'][0])
            y=geometry([bs[use],bs[use]],cd,B,small,grouped=True,merkle_layout='coset',first_group=ck)
            assert x['bytes']==run['compression_opening_bytes'] and y['bytes']==run['call_opening_bytes']
            assert x['bytes']+y['bytes']+report['fixed_bytes']==run['combined_bytes'];full+=1
    result=dict(status='PASS',exhaustive_small_packing_cases=checks,independent_selected_geometry_replays=full,shared_root_layout_checks=full)
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
