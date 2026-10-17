"""Full-witness diagnostic for packed claim reduction, NOT a PCS verifier."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from packed_claim_handoff import derive_handoff, packing_context
from check_whir_handoff import P, add, sub, mul

ZERO=(0,0,0,0);ONE=(1,0,0,0)


def direct_mle(values,point):
    # Independent Boolean equality-weight sum, rather than adjacent folding.
    assert len(values)==1<<len(point)
    result=ZERO
    for i,value in enumerate(values):
        weight=ONE
        for bit,r in enumerate(point):weight=mul(weight,r if i>>bit&1 else sub(ONE,r))
        result=add(result,mul(weight,value))
    return result


def expected(rows,packing,point):
    width=len(rows[0]);result=[]
    for start in range(0,width,packing):
        values=[(row[start+c],0,0,0) if start+c<width else ZERO
                for c in range(packing) for row in rows]
        result.append(list(direct_mle(values,point)))
    return result


def main():
    binary,source,report=sys.argv[1:]
    raw=json.loads(Path(source).read_text())['rows']
    rows=[r[:7] for r in raw[:4]]
    point=[(17,19,23,29),(31,37,41,43)]
    claims=[direct_mle([(r[c],0,0,0) for r in rows],point) for c in range(7)]
    results=[];rejected=0;bindings=0;malformed=0
    for packing in (1,2,8):
        with tempfile.TemporaryDirectory(prefix='near-packed-handoff-') as d:
            src,dst=Path(d)/'in.json',Path(d)/'out.json'
            src.write_text(json.dumps({'rows':rows,'packing':packing,'indices':[0]}))
            subprocess.run([binary,str(src),str(dst)],check=True,capture_output=True)
            commitment=json.loads(dst.read_text())
        import struct
        root=struct.pack('<12I',*commitment['root'])
        assert bytes.fromhex(commitment['context_hex'])==packing_context(2,7,packing)
        args=[b'canonical-fixture-statement',b'source/current/branch0',root,2,7,packing,point,claims]
        handoff=derive_handoff(*args)
        assert handoff['kind']=='undischarged-packed-pcs-obligation'
        assert handoff['lane_claims']==expected(rows,packing,handoff['packed_point'])
        assert derive_handoff(*args)==handoff
        for col in range(7):
            for coefficient in range(4):
                bad=copy.deepcopy(args);bad[7]=[list(v) for v in claims]
                bad[7][col][coefficient]=(bad[7][col][coefficient]+1)%P
                changed=derive_handoff(*bad)
                assert changed['lane_claims']!=expected(rows,packing,changed['packed_point'])
                assert changed['transcript_seed_hex']!=handoff['transcript_seed_hex']
                rejected+=1
        for index in (0,1,2,6):
            bad=copy.deepcopy(args)
            if index==2:bad[index]=bytes([root[0]^1])+root[1:]
            elif index==6:bad[index]=[list(v) for v in point];bad[index][0][0]+=1
            else:bad[index]+=b'changed'
            changed=derive_handoff(*bad)
            assert changed['transcript_seed_hex']!=handoff['transcript_seed_hex']
            if packing>1:assert changed['packed_point'][2:]!=handoff['packed_point'][2:]
            bindings+=1
        for index,value in [(2,root[:-1]),(3,0),(4,8),(5,3),(6,point[:-1]),
                            (7,claims[:-1]),(7,[(P,0,0,0)]+claims[1:])]:
            bad=copy.deepcopy(args);bad[index]=value
            try:derive_handoff(*bad)
            except ValueError:malformed+=1
            else:raise AssertionError('malformed handoff accepted')
        results.append({'packing':packing,'root_hex':root.hex(),'handoff':handoff})
    result={'status':'PASS','cases':results,'changed_claims_detected_with_full_witness':rejected,
            'transcript_binding_checks':bindings,'malformed_rejections':malformed,
            'scope':'Produces PCS obligations only; full witness used by tests to check their truth',
            'limits':['No PCS opening protocol integrated','Ext4 diagnostic is not PQ security profile',
                      'Observed mutation rejection is not a probabilistic soundness proof',
                      'Enclosing AIR transcript binding remains an integration obligation']}
    Path(report).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS',rejected,'changed claims;',bindings,'bindings;',malformed,'malformed inputs')


if __name__=='__main__':main()
