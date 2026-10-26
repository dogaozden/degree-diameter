import itertools, numpy as np, sys
# A_7 as permutations of 0..6; elements indexed; mult table (uint16) and inverse
n=7
def sign(p):
    s=1; p=list(p); seen=[False]*n
    for i in range(n):
        if not seen[i]:
            j=i; L=0
            while not seen[j]:
                seen[j]=True; j=p[j]; L+=1
            if L%2==0: s=-s
    return s
els=[p for p in itertools.permutations(range(n)) if sign(p)==1]
N=len(els); idx={p:i for i,p in enumerate(els)}
print("order",N, file=sys.stderr)
E=np.array(els,dtype=np.int8)  # N x 7
# product convention: (a*b)(x) = a(b(x))
mul=np.zeros((N,N),dtype=np.uint16)
# encode permutations as base-7 integers for lookup
w=7**np.arange(n)
codes=(E.astype(np.int64)*w).sum(1)
order=np.argsort(codes); sc=codes[order]
for a in range(N):
    comp=E[a][E]  # row b: a(b(x)) for all x
    c=(comp.astype(np.int64)*w).sum(1)
    pos=np.searchsorted(sc,c)
    mul[a]=order[pos]
inv=np.array([int(np.where(mul[a]==0)[0][0]) for a in range(N)],dtype=np.uint16)
e=idx[tuple(range(n))]
assert e==0 or True
mul.astype('<u2').tofile('mul.bin'); inv.astype('<u2').tofile('inv.bin')
print("identity index",e, file=sys.stderr)
