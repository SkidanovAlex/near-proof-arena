"""Independent algebraic verifier for native arbitrary-weight stacking sumcheck.

Transcript challenge replay and full stacked-matrix evaluations are checked by
Rust. This verifier checks the captured challenges' reduction equations, not a
standalone PCS or Fiat-Shamir proof.
"""
import copy,gzip,json
from pathlib import Path
import pq384_terminal_gkr as g
from swirl_weighted_stack_ext import kernels
ROOT=Path(__file__).resolve().parents[2]/'results/swirl-security-review'
OUT=ROOT/'weighted-native-sumcheck'


def total(xs):
    result=g.ZERO
    for x in xs:result=g.add(result,x)
    return result


def horner(coeffs,x):
    result=g.ZERO
    for c in reversed(coeffs):result=g.add(g.mul(result,x),tuple(c))
    return result


def verify(proof):
    vectors = proof['s0'] + proof['u'] + proof['claim'] + proof['r']
    vectors += [v for row in proof['rounds'] + proof['openings'] for v in row]
    assert all(isinstance(v,list) and len(v)==4 and
               all(type(x) is int and 0<=x<2013265921 for x in v) for v in vectors)
    capture=json.loads(gzip.decompress((ROOT/'committed-witness/point-capture.jsonl.gz').read_bytes()))
    layouts=json.loads((ROOT/'committed-witness/layouts.json').read_text())
    source=json.loads(gzip.decompress((ROOT/'committed-witness/openings.json.gz').read_bytes()))
    pairs=json.loads(gzip.decompress((ROOT/'witness-dag-gkr/native-pairs.json.gz').read_bytes()))
    lskip=capture['l_skip'];stack=layouts[0]['height'].bit_length()-1;n=stack-lskip
    assert proof['r']==capture['r'] and proof['claim']==[pairs['claim']]
    assert len(proof['s0'])==2*((1<<lskip)-1)+1 and len(proof['rounds'])==n and len(proof['u'])==1+n
    assert len(proof['openings'])==len(layouts)
    u=[tuple(x) for x in proof['u']];r=[tuple(x) for x in capture['r']]
    assert g.mul(total(tuple(x) for x in proof['s0'][::1<<lskip]),g.base(1<<lskip))==tuple(pairs['claim'])
    claim=horner(proof['s0'],u[0])
    for p,x in zip(proof['rounds'],u[1:]):
        assert len(p)==2
        y1,y2=map(tuple,p);y0=g.sub(claim,y1)
        # Explicit interpolation through 0,1,2.
        claim=total([g.mul(y0,g.mul(g.mul(g.sub(x,g.ONE),g.sub(x,g.base(2))),g.base(pow(2,-1,2013265921)))),
                     g.mul(y1,g.mul(x,g.sub(g.base(2),x))),
                     g.mul(y2,g.mul(g.mul(x,g.sub(x,g.ONE)),g.base(pow(2,-1,2013265921))))])
    lookup={};com=1
    for t,o in enumerate(source):
        lookup[o['air'],0]=(0,t)
        for part in range(1,len(o['parts'])):lookup[o['air'],part]=(com,0);com+=1
    slices={}
    for com,layout in enumerate(layouts):
        assert len(proof['openings'][com])==layout['width']
        for matrix,col,target,start,height in layout['slices']:slices[com,matrix,col]=(target,start,height)
    coeffs=[[g.ZERO]*l['width'] for l in layouts]
    for pair in pairs['pairs']:
        com,matrix=lookup[pair['air'],pair['opening_part']]
        target,start,height=slices[com,matrix,pair['column']]
        a,b=kernels(lskip,stack,height,start,r,u)
        value=g.add(g.mul(a,tuple(pair['current_weight'])),g.mul(b,tuple(pair['rotated_weight'])))
        coeffs[com][target]=g.add(coeffs[com][target],value)
    final=total(g.mul(c,tuple(v)) for cs,vs in zip(coeffs,proof['openings']) for c,v in zip(cs,vs))
    assert final==claim
    return coeffs


def main():
    proof=json.loads((OUT/'proof.json').read_text());coeffs=verify(proof)
    mutations=[]
    for path in [('s0',0,0),('rounds',0,0,0),('u',0,0),('openings',0,0,0)]:
        p=copy.deepcopy(proof);v=p
        for key in path[:-1]:v=v[key]
        v[path[-1]]=(v[path[-1]]+1)%2013265921
        try:verify(p)
        except AssertionError:mutations.append(str(path))
        else:raise AssertionError(('mutation accepted',path))
    field_elements=len(proof['s0'])+2*len(proof['rounds'])+sum(map(len,proof['openings']))
    result=dict(status='NATIVE_ARBITRARY_WEIGHT_SUMCHECK_ALGEBRA_VERIFIED',
        sumcheck_extension_elements=len(proof['s0'])+2*len(proof['rounds']),
        terminal_opening_elements=sum(map(len,proof['openings'])),field_elements=field_elements,
        ext4_field_payload_bytes=field_elements*16,negative_checks=mutations,
        limitations=['Terminal evaluations checked against full matched witness, not a fresh PCS opening proof.',
                    'Native transcript replay tested; Python checks captured challenge equations only.',
                    'GKR/native controls still depend on old full-opening transcript. No compression/QROM/PQ128 theorem.'])
    (OUT/'coefficients.json').write_text(json.dumps(coeffs)+'\n')
    (OUT/'report.json').write_text(json.dumps(result,indent=2)+'\n');print(result)

if __name__=='__main__':main()
