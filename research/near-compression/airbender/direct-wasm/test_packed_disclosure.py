"""Native commitment → independent claims → complete small packed opening."""
import copy
import json
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
from packed_disclosure import prove_disclosure, verify_disclosure
from test_packed_claim_handoff import direct_mle
from pq384_primitives import P


def run(binary,rows,packing):
    n,width=len(rows),len(rows[0]);degree=n*packing
    with tempfile.TemporaryDirectory(prefix='near-packed-disclosure-') as d:
        src,dst=Path(d)/'input.json',Path(d)/'output.json'
        src.write_text(json.dumps({'rows':rows,'packing':packing,'indices':[0]}))
        subprocess.run([binary,str(src),str(dst)],check=True,capture_output=True)
        root=struct.pack('<12I',*json.loads(dst.read_text())['root'])
    point=[(3+11*i,5+13*i,7+17*i,11+19*i) for i in range(n.bit_length()-1)]
    claims=[direct_mle([(r[c],0,0,0) for r in rows],point) for c in range(width)]
    proof=prove_disclosure(rows,packing)
    # Check monomial coefficients using independent inclusion-exclusion.
    for lane,cs in enumerate(proof['coefficients']):
        for mask,c in enumerate(cs):
            total=0;subset=mask
            while True:
                col=lane*packing+subset//n
                value=rows[subset%n][col] if col<width else 0
                total+=(-1 if (mask.bit_count()-subset.bit_count())%2 else 1)*value
                if subset==0:break
                subset=(subset-1)&mask
            assert c==total%P
    args=dict(statement=b'table-opening-fixture',parent_binding=b'current-branch',
              expected_root=root,log_rows=n.bit_length()-1,width=width,packing=packing,
              row_point=point,column_claims=claims)
    assert verify_disclosure(proof,**args)
    rejected=0
    def reject(p,a):
        nonlocal rejected
        try:verify_disclosure(p,**a)
        except ValueError:rejected+=1
        else:raise AssertionError('invalid packed opening accepted')
    for lane,cs in enumerate(proof['coefficients']):
        for j in range(degree):
            bad=copy.deepcopy(proof);bad['coefficients'][lane][j]=(cs[j]+1)%P
            reject(bad,args)
    for col in range(width):
        for k in range(4):
            bad=copy.deepcopy(args);bad['column_claims']=[list(v) for v in claims]
            bad['column_claims'][col][k]=(bad['column_claims'][col][k]+1)%P
            reject(proof,bad)
    for key,value in [('expected_root',bytes([root[0]^1])+root[1:]),
                      ('log_rows',7),('packing',3),('column_claims',claims[:-1]),
                      ('row_point',point[:-1])]:
        bad=copy.deepcopy(args);bad[key]=value;reject(proof,bad)
    for key,value in [('profile','old'),('extra',0),('coefficients',proof['coefficients'][:-1])]:
        bad=copy.deepcopy(proof);bad[key]=value;reject(bad,args)
    for value in [P,-1,True]:
        bad=copy.deepcopy(proof);bad['coefficients'][0][0]=value;reject(bad,args)
    bad=copy.deepcopy(proof);bad['coefficients'][0].pop();reject(bad,args)
    # The same true vector can be opened under another statement/branch: this
    # disclosure is universal, while challenges and enclosing proofs are bound.
    bad=copy.deepcopy(args);bad['statement']+=b'other';bad['parent_binding']+=b'other'
    assert verify_disclosure(proof,**bad)
    return {'rows':n,'width':width,'packing':packing,'root_hex':root.hex(),
            'proof_json_bytes':len(json.dumps(proof,separators=(',',':')).encode()),
            'coefficient_bytes':sum(len(cs) for cs in proof['coefficients'])*4,
            'mutations_rejected':rejected}


def main():
    binary,source,report=sys.argv[1:]
    source_rows=json.loads(Path(source).read_text())['rows']
    rows=[r[:7] for r in source_rows[:4]]
    cases=[run(binary,rows,p) for p in (1,2,8)]
    cases.append(run(binary,[[P-1,2,19],[31,P-2,7]],2))
    result={'status':'PASS','cases':cases,
            'scope':'Complete small packed-point opening; verifier uses no external witness',
            'limits':['Coefficient disclosure not zero knowledge','Original vector reduction remains probabilistic',
                      'No integration with complete AIR proof transcript yet','DiagnosticExt4 not128-bitPQ security',
                      'Bytes are standalone opening proof, not fullNEAR proof']}
    Path(report).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
