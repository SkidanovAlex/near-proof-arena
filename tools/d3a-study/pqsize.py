import math
# final-layer size model, PQ: per-round query soundness target T bits (t^2 * eps_rbr loss with t=2^64 -> ~2^-256 needed;
# T=260 incl. slack), grinding z classical bits -> z/2 PQ bits; digest D bytes; ext element E bytes.
def size(logn, logb, bq, T=260, z=32, D=64, E=40, weq=300, trees=3, ar=3, flog=6):
    q=math.ceil((T-z/2)/bq); L=logn+logb; sh=math.log2(q)
    per=4*weq + trees*D*max(0,L-sh)
    d=L; fri=0; layers=0
    while d-ar>=flog+logb:
        d-=ar; layers+=1; fri+=(2**ar)*E + D*max(0,d-sh)
    per+=fri
    fixed=D*(trees+layers)+E*2**flog+E*2*weq
    return q,q*per+fixed
print("regime blowup trace  q  size(KB)  [D=64B SHA-512 | D=48B SHA-384 | classical ref D=32,T=192,z=32 full]")
for logb in (4,6,8):
  rho=2**-logb
  for nm,b in (('UDR',-math.log2((1+rho)/2)),('Johnson',0.5*logb-0.1)):
    for logn in (14,16,18):
      if logn+logb>27: continue
      q,s64=size(logn,logb,b); _,s48=size(logn,logb,b,D=48); qc,sc=size(logn,logb,b,T=192,z=64,D=32,E=32)
      print(f"{nm:8s} 2^{logb} 2^{logn} q={q:4d} {s64/1e3:7.0f} | {s48/1e3:7.0f} | q={qc} {sc/1e3:6.0f}")
