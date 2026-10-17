"""Independent weighted-equation versus layered-circuit parity."""
import argparse
import json
from pathlib import Path
import random
import private_merkle_proof as p


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--statement',type=Path,required=True)
    ap.add_argument('--example',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    st=json.loads(a.statement.read_text());example=json.loads(a.example.read_text());public=example['statement']
    layout,seed,binding,program=p.compile_layout(st['spec'],st['roots'],public,8)
    eq=p.route.flatten_equations(program);t=p.Transcript(seed)
    point=[tuple(x) for x in t.draw(b'private-merkle-routing-after-all-roots',(len(eq)-1).bit_length(),8)[0]]
    assert t.seed==binding;weights=p.call.g.eqs(point);g=p.call.g
    rng=random.Random(133356);checks=0
    n=program['row_count'];rows=example['rows']
    cases=[[g.base(rows[r][c]) if c<179 else g.ZERO for c in range(256) for r in range(n)],
           [g.ZERO]*layout['private_capacity'],
           [tuple(rng.randrange(p.route.P) for _ in range(8)) for _ in range(layout['private_capacity'])]]
    for index,private in enumerate(cases):
        expected=g.ZERO
        for equation,w in zip(eq,weights):
            value=g.sub(g.ZERO,g.base(equation['constant']))
            for slot,coefficient in equation['terms']:
                value=g.add(value,g.mul(private[slot],g.base(coefficient%p.route.P)))
            expected=g.add(expected,g.mul(w,value))
        got=g.values(layout,private)[-1][layout['root']]
        assert got==expected
        if index==0:assert got==g.ZERO
        else:assert got!=g.ZERO
        checks+=1
    report=dict(status='PASS',independent_layered_equation_cases=checks,equations=len(eq),
        private_capacity=layout['private_capacity'],layer_count=len(layout['layers']),
        scope='Concrete generated circuit parity including negative signed coefficients. Not a universal compiler proof or cryptographic soundness theorem.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
