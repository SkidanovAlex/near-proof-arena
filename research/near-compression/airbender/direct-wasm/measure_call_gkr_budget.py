"""Read exact retained geometry; report only ideal algebraic error terms."""
import argparse,gzip,hashlib,json,math
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2]
    capture=package/'results/call-layer-certificates/case-0.json.gz'
    bundle=json.loads(gzip.decompress(capture.read_bytes()));layout=bundle['layout']
    parity=json.loads((package/'results/call-array-parity/report.json').read_text())
    count=parity['scenarios'][0]['equations'];dimension=(count-1).bit_length()
    def log(size):
        assert size>0 and size&(size-1)==0
        return size.bit_length()-1
    # Each GKR layer sums over two copies of its predecessor index space.
    sizes=[layout['input_size']]+[len(layer) for layer in layout['layers'][:-1]]
    rounds=list(reversed([log(size) for size in sizes]))
    gkr_numerator=sum(4*m+1 for m in rounds)
    modulus=2013265921;degree=4;field_size=modulus**degree
    numerator=dimension+gkr_numerator
    report=dict(status='IDEAL_COMPONENT_BOUND_ONLY',equations=count,batching_dimension=dimension,
        layers=len(rounds),input_logs_output_to_input=rounds,gkr_degree_numerator=gkr_numerator,
        batching_degree_numerator=dimension,union_numerator=numerator,field_size=str(field_size),
        ideal_component_bound=f'{numerator}/{field_size}',negative_log2_ideal_component_bound=math.log2(field_size)-math.log2(numerator),
        terminal_opening_error='EXPLICIT_UNBOUNDED_TERM',
        assumptions=['Uniform independent ideal field challenges','Fixed source residuals before batching',
            'Checked compiler structure and exact root-query/zero-claim binding','GKR evaluated verifier path refinement',
            'Each challenge has the existing quadratic/linear degree bound'],
        scope='Parameter instantiation of batching and GKR terms only. Not total soundness, not a lower bound on actual attack probability, not Fiat-Shamir/QROM or PQ128 certification. PCS/commitment errors and sampling/hash reductions are excluded. The union combines conditional component bounds; a complete outer-batching-to-GKR transcript theorem remains open.',
        source_sha256={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [capture,package/'NearCompression/CallGKRRoot.lean',package/'NearCompression/CallPadding.lean']})
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
