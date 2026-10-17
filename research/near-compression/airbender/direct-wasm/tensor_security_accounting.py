"""Exact conditional arithmetic for proved finite extraction, quadratic sumcheck, and folding bounds.

This does not instantiate the protocol-to-tensor, residual, field, commitment,
or QROM bridges. It must not be used as a security certification.
"""
from fractions import Fraction
import json
from pathlib import Path
import sys

P=2013265921
N=524288
D=131072
T=393217
n=17
assert 2*N+D-1<3*T
stages=[N//(2**(i+1)) for i in range(n)]
fold_error=sum(max(x,2) for x in stages)
tensor_error=n*max(N,2)
sumcheck_error=2*n
functional_error=tensor_error+sumcheck_error
combined=functional_error+fold_error
assert D-1<T and 2*(N-T)+D<=N

def fraction_record(numerator,denominator):
    f=Fraction(numerator,denominator)
    bits=0
    while f*2**(bits+1)<=1:bits+=1
    return dict(numerator=f.numerator,denominator=f.denominator,integer_bits_supported_by_this_bound=bits)

report=dict(status='conditional arithmetic only',parameters=dict(p=P,N=N,D=D,T=T,tensor_coordinates=n),
    tensor_error_numerator=tensor_error,weighted_sumcheck_error_numerator=sumcheck_error,
    functional_opening_error_numerator=functional_error,fold_error_numerator=fold_error,union_numerator=combined,
    ideal_ext4_tensor=fraction_record(tensor_error,P**4),ideal_ext4_union=fraction_record(combined,P**4),
    minimum_extension_degree_for_isolated_union={str(bits):next(e for e in range(1,30) if P**e>=combined*2**bits) for bits in (128,192,256)},
    assumptions=['Sample set has exactly p^e distinct field elements and independent uniform coordinates',
                 'Tensor extraction is instantiated with the same fixed actual weighted-source tensor and T',
                 'FunctionalOpeningReduction establishes the abstract initial candidate-event bound; executable sparse-lift/current-next mapping remains separate',
                 'Union with folding is arithmetic here; transcript-prefix and full protocol composition remain separate'],
    excluded=['Query tail','Other sumcheck/GKR/bus collision errors (the first weighted quadratic sumcheck is included)','Hash commitment errors','Sampler refinement and rejection failure','Fiat-Shamir/QROM losses'],
    security_certified=False)
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
