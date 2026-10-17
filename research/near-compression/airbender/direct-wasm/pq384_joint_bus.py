"""Compose existing SHA384 AIR reductions with new joint PCS experiment.

The AIR transcript stays v2; its branch obligations are inputs to a NEW joint
opening transcript. Soundness of the extra reduction/batching is outstanding.
"""
import pq384_global_bus as bus
import pq384_joint_opening as joint
from pq384_primitives import require
PROFILE='near-pq384-joint-bus-v1'

def arguments(prefix,spec,roots):
    require(type(prefix)is dict and set(prefix)=={'profile','aux_roots','finals','tables'} and prefix['profile']==bus.PROFILE,'prefix fields')
    st,t,alpha,gamma=bus.begin(spec,roots);ars=[bus.pcs.decode_hash(v) for v in prefix['aux_roots']]
    bus.initialize_aux(t,spec,ars,prefix['finals']);result=[]
    require(isinstance(prefix['tables'],list) and len(prefix['tables'])==len(roots),'prefix table count')
    for ti,part in enumerate(prefix['tables']):
        result.extend(bus.verify_table_reduction(part,spec,st,t,alpha,gamma,ti,prefix['finals'][ti],[roots[ti],ars[ti]]))
    require(bus.global_fingerprint_balance(spec,prefix['finals'],alpha,gamma),'fingerprint product equality')
    return result

def verify(proof,spec,roots):
    require(type(proof)is dict and set(proof)=={'profile','air','joint'} and proof['profile']==PROFILE,'joint bus fields')
    return joint.verify(proof['joint'],arguments(proof['air'],spec,roots))

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    proof=json.loads(Path(sys.argv[1]).read_text());trusted=json.loads(Path(sys.argv[2]).read_text())
    assert verify(proof,trusted['spec'],[bytes.fromhex(v) for v in trusted['roots']])
    print('PASS: joint-opening full AIR diagnostic; joint soundness not established')
