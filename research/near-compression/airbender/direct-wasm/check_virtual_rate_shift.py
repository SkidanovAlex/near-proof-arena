"""Algebra-only parity for arbitrary source words, not Merkle authentication.
The production quartet transform is compared to two sequential pair decodes.
"""
import hashlib,json,random
from pathlib import Path
import pq384_ext8_rate_shift as r

def pair(a,b,x,challenge):
    even=r.e.scale(r.e.add(a,b),pow(2,-1,r.e.P))
    odd=r.e.scale(r.e.sub(a,b),pow(2*x%r.e.P,-1,r.e.P))
    return r.e.add(r.e.mul(r.e.sub(r.e.ONE,challenge),even),r.e.mul(challenge,odd))

def run():
    e=r.e;rng=random.Random(3117);omega=pow(440564289,(1<<27)//128,e.P)
    draw=lambda:tuple(rng.randrange(e.P) for _ in range(8))
    challenges=[(e.ZERO,e.ZERO),(e.ZERO,e.ONE),(e.ONE,e.ZERO),(e.ONE,e.ONE),(draw(),draw())]
    old=r.p.read_opening;checked=0
    try:
        for _ in range(4):
            word=[e.base(rng.randrange(e.P)) for _ in range(128)]
            # Authentication deliberately bypassed: isolates transform algebra.
            r.p.read_opening=lambda opening,root,ctx,half,index,scalar:(word[index],word[index+64])
            for r0,r1 in challenges:
                first=[pair(word[i],word[i+64],pow(omega,i,e.P),r0) for i in range(64)]
                for i in range(32):
                    expected=pair(first[i],first[i+32],pow(omega,2*i,e.P),r1)
                    actual=r.folded_query([None,None],None,None,i,[r0,r1])
                    assert actual==expected
                    checked+=1
    finally:
        r.p.read_opening=old
    report=dict(status='PASS',arbitrary_source_words=4,comparisons=checked,
        cases='All32 cosets, zero/one challenges and full-extension challenges; two pair decodes versus production inverse-DFT quartet transform.',
        limitations=['read_opening mocked: no authentication/commitment claim.','Executable parity is not kernel refinement of the Python implementation.'],
        source_sha256={n:hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest() for n in [Path(__file__).name,'pq384_ext8_rate_shift.py']})
    (Path(__file__).resolve().parents[2]/'results/virtual-rate-shift-runtime.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':run()
