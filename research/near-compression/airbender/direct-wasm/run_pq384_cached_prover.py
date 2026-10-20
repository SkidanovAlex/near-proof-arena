"""Full-height cached opening and separate-process reference verification."""
import argparse,json,subprocess,sys,time,hashlib
from array import array
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True)
    ap.add_argument('--library',required=True);ap.add_argument('--cache',required=True)
    ap.add_argument('--source',required=True);ap.add_argument('--output-dir',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir)
    from pq384_native_fft import NativeFFT
    from pq384_source_cache import SourceCache
    from pq384_cached_prover import prove_cached
    from pq384_batched_codec import encode
    from pq384_primitives import P,Transcript
    native=NativeFFT(a.library);out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True)
    rows=json.loads(Path(a.source).read_text())['rows'];n=len(rows);width=len(rows[0])
    assert n&(n-1)==0 and all(len(row)==width for row in rows)
    assert all(type(v)is int and 0<=v<P for row in rows for v in row)
    m=json.loads((Path(a.cache)/'manifest.json').read_text());root=bytes.fromhex(m['root_hex'])
    statement=b'NEAR-full-height-actual-source-opening-diagnostic-Q8-v1'
    t=Transcript(statement);t.commit(b'source-root',root)
    draws,_=t.draw(b'independent-row-point',n.bit_length()-1,4);point=[tuple(v) for v in draws]
    started=time.perf_counter();claims=[]
    for col in range(width):
        words=array('I',(v for row in rows for v in (row[col],0,0,0)))
        for r in point:words=native.fold_words(words,r)
        claims.append(list(words))
    claim_seconds=time.perf_counter()-started
    # Independent direct multilinear evaluation for three complete source columns.
    from check_whir_handoff import add,mul,sub
    one=(1,0,0,0);zero=(0,0,0,0);ws=[one]
    for r in reversed(point):
        ws=[v for w in ws for v in (mul(w,sub(one,r)),mul(w,r))]
    for col in sorted(set([0,width//2,width-1])):
        got=zero
        for row,w in zip(rows,ws):got=add(got,tuple(v*row[col]%P for v in w))
        assert list(got)==claims[col]
    args=dict(statement=statement,parent_binding=b'diagnostic-no-enclosing-AIR-transcript',
              expected_root=root,log_rows=n.bit_length()-1,width=width,packing=m['packing'],
              row_point=point,column_claims=claims)
    del rows,ws
    started=time.perf_counter()
    with SourceCache(a.cache,**{k:args[k] for k in ('expected_root','log_rows','width','packing')}) as cache:
        proof=prove_cached(cache,native,**args)
    prover_seconds=time.perf_counter()-started
    serial={k:(v.hex() if isinstance(v,bytes) else v) for k,v in args.items()}
    (out/'statement.json').write_text(json.dumps(serial));(out/'proof.json').write_text(json.dumps(proof))
    binary=encode(proof,args['log_rows'],width,args['packing']);(out/'proof.bin').write_bytes(binary)
    started=time.perf_counter()
    verifier=subprocess.run([sys.executable,str(Path(a.reference_dir)/'verify_pq384_batched_fold.py'),
        str(out/'proof.bin'),str(out/'statement.json'),'--binary'],check=True,capture_output=True,text=True)
    verify_seconds=time.perf_counter()-started
    report=dict(status='PASS',rows=n,width=width,packing=args['packing'],degree=n*args['packing'],
        rounds=len(proof['rounds']),queries_per_round=8,proof_bytes=len(binary),
        source_root=root.hex(),independent_full_column_checks=3,
        claim_seconds=claim_seconds,prover_seconds=prover_seconds,verify_seconds=verify_seconds,
        verifier_output=verifier.stdout.strip(),proof_sha256=hashlib.sha256(binary).hexdigest(),
        scope='Actual-source batched opening diagnostic; no enclosing AIR proof or security certification')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
