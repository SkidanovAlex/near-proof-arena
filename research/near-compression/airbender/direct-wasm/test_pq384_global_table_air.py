"""Pure/native AIR parity and AIR/PCS branch linkage rejection."""
import argparse,copy,json,os,sys
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--fixture',required=True)
    ap.add_argument('--folded-library',required=True);ap.add_argument('--fft-library',required=True);a=ap.parse_args()
    sys.path.append(a.reference_dir);os.environ['NEAR_PQ384_FFT_LIB']=a.fft_library
    import pq384_global_table_air as air
    import pq384_global_table_codec as codec
    from pq384_native_global_table_air import prove_native
    f=json.loads(Path(a.fixture).read_text());spec={k:f[k] for k in ('air','table_index','public')}
    spec.update(log_rows=3,packing=16,terminal_degree=1);root=air.source_commitment(f['rows'],spec)
    ref=air.prove(spec,root,f['rows']);actual,_=prove_native(spec,root,f['rows'],folded_library=a.folded_library)
    assert actual==ref and air.verify_table_local(actual,spec,root)
    data=codec.encode(actual,spec,root);assert codec.decode(data,spec,root)==actual
    rejected=0
    def reject(proof,s=spec,r=root):
        nonlocal rejected
        try:air.verify_table_local(proof,s,r)
        except ValueError:rejected+=1
        else:raise AssertionError('invalid proof accepted')
    args=air.verify_reduction(actual,spec,root);args['parent_binding']=b'wrong-branch'
    bad=copy.deepcopy(actual);bad['opening']=air.prove_opening(f['rows'],spec,**args);reject(bad)
    rows=copy.deepcopy(f['rows']);rows[2][0]+=1;r=air.source_commitment(rows,spec)
    bad=air.prove(spec,r,rows);reject(bad,spec,r)
    for key in ['current_evals','next_evals']:
        bad=copy.deepcopy(actual);bad['shift_reduction'][key][0][0]^=1;reject(bad)
    bad=copy.deepcopy(actual);bad['column_claims'][0][0]^=1;reject(bad)
    for malformed in [data[:-1],data+b'\0',b'X'+data[1:]]:
        try:codec.decode(malformed,spec,root)
        except ValueError:rejected+=1
        else:raise AssertionError('bad codec input accepted')
    print(json.dumps(dict(status='PASS',exact_reference_parity=True,binary_roundtrip=True,bytes=len(data),negative_checks=rejected)))

if __name__=='__main__':main()
