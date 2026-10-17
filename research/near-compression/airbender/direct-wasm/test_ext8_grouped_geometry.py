"""Independent full-coset enumeration and exhaustive schedule check."""
from itertools import product
from screen_ext8_grouped_geometry import geometry


def schedules(n):
    if n==0:yield []
    for k in range(1,min(4,n)+1):
        for rest in schedules(n-k):yield [k]+rest


def cost(branches,D,B,samples,groups,layout):
    def opening(half,width,domain,k):
        # Enumerate EVERY scalar in the coset, then quotient by paired leaves.
        indices={(s+j*(domain//(1<<k)))%half for s in samples for j in range(1<<k)}
        if layout=='coset':
            group_size=max(1,half//(domain//(1<<k)))
            count=half//group_size
            # Pack the periodic paired-leaf positions into a single leaf.
            indices={i%count for i in indices};half=count;width*=group_size
        leaves=len(indices)*width;auth=0
        while half>1:
            auth+=48*len({i^1 for i in indices}-indices)
            indices={i//2 for i in indices};half//=2
        return leaves+auth
    total=40+192*(D.bit_length()-1)+48*len(groups);d=D;seen=set()
    for pos,k in enumerate(groups):
        if pos==0:
            for b in branches:
                key=(b['root'],b['log_rows'],b['width'],b['packing'])
                if key in seen:continue
                seen.add(key);source_degree=(1<<b['log_rows'])*b['packing']
                total+=opening(B*source_degree//2,8*len(b['lanes']),B*d,k)
        else:total+=opening(B*d//2,64,B*d,k)
        d>>=k
    assert d==1
    return total


def main():
    count=0
    for n,B in product((2,4,7),(4,16,64)):
        D=1<<n
        branches=[dict(root='a',log_rows=n-1,width=3,packing=2,lanes=[None]*2),dict(root='b',log_rows=1,width=2,packing=1,lanes=[None]*2)]
        branches.append(dict(branches[0]))
        for samples,layout in product(([0,1,1,3],[B*D-1,2,7]),('paired','coset')):
            expected=min(cost(branches,D,B,samples,path,layout) for path in schedules(n))
            actual=geometry(branches,D,B,samples,grouped=True,merkle_layout=layout)
            assert actual['bytes']==expected
            assert cost(branches,D,B,samples,actual['groups'],layout)==expected
            assert geometry(branches,D,B,samples,grouped=False,merkle_layout=layout)['bytes']==cost(branches,D,B,samples,[1]*n,layout)
            count+=1
    print('PASS',count,'independent exhaustive schedule/coset cases')

if __name__=='__main__':main()
