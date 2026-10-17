import argparse,json,sys,subprocess,os,time,random
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--input-directory',required=True);ap.add_argument('--output-directory',required=True);ap.add_argument('--baseline-bytes',type=int);ap.add_argument('--quick-negatives',action='store_true');a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_compact_gkr_bus_codec as codec
    from pq384_primitives import P
    rng=random.Random(873);primitive_checks=0
    for tags in (False,True):
        for n in range(40):
            values=[rng.randrange(P) if i%4 else 0 for i in range(n)];w=codec.compact.Writer();w.fields(values,tags);w.raw(b'boundary');w.fields(values,tags)
            r=codec.compact.Reader(w.finish());assert r.fields(n,tags)==values;assert r.raw(8)==b'boundary';assert r.fields(n,tags)==values;r.finish();primitive_checks+=1
    primitive_negatives=0
    for mode in ('padding','field','zero-tag'):
        w=codec.compact.Writer()
        if mode=='padding':w.bitword(1,31);data=bytearray(w.finish());data[-1]|=128
        elif mode=='field':w.bitword(P,31);data=w.finish()
        else:w.bitword(1,1);w.bitword(0,31);data=w.finish()
        try:r=codec.compact.Reader(bytes(data));r.fields(1,mode=='zero-tag');r.finish()
        except ValueError:primitive_negatives+=1
        else:raise AssertionError(mode)
    inp=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);s=json.loads((inp/'statement.json').read_text());proof=json.loads((inp/'proof.json').read_text());roots=[bytes.fromhex(x) for x in s['roots']];start=time.perf_counter()
    data=codec.encode(proof,s['spec'],roots);decoded=codec.decode(data,s['spec'],roots);assert decoded==proof;(out/'proof.bin').write_bytes(data)
    env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir]);verified=subprocess.run([sys.executable,str(Path(codec.__file__)),str(out/'proof.bin'),str(inp/'statement.json')],env=env,check=True,capture_output=True,text=True)
    neg=0
    def reject(b):
        nonlocal neg
        try:codec.decode(b,s['spec'],roots)
        except (ValueError,KeyError,TypeError,IndexError):neg+=1
        else:raise AssertionError('malformed compact proof accepted')
    reject(data+b'\0');bad=bytearray(data);bad[-1]^=1;reject(bytes(bad))
    if not a.quick_negatives:
        reject(data[:-1]);reject(data[:len(codec.MAGIC)+48*len(roots)]);reject(b'X'+data[1:])
        for offset in (len(codec.MAGIC),len(data)//3,len(data)//2,2*len(data)//3):
            bad=bytearray(data);bad[offset]^=1;reject(bytes(bad))
    report=dict(status='PASS',whole_proof_bytes=len(data),baseline_bytes=a.baseline_bytes,saving_bytes=a.baseline_bytes-len(data) if a.baseline_bytes else None,
        source_commitments_included=48*len(roots),exact_original_proof_roundtrip=True,unchanged_roots_transcript_queries=True,
        omitted_linear_coefficients=sum(s['spec']['log_rows'])+sum(len(x['rounds']) for x in proof['gkr']['layers'])+len(proof['opening']['reduction'])+len(proof['opening']['rounds']),
        bitcodec_roundtrips=primitive_checks,bitcodec_negative_checks=primitive_negatives,proof_negative_checks=neg,
        fresh_process_verification=verified.stdout.strip(),test_seconds=time.perf_counter()-start,
        scope='Lossless codec of SAME diagnostic proof; no stronger soundness or query selection')
    (out/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))

if __name__=='__main__':main()
