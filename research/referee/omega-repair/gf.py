# GF(q) as lookup tables for q in {2,3,4,5,7,8,9,11,13}
import numpy as np
def make_gf(q):
    if q in (2,3,5,7,11,13):
        p=q
        add=np.array([[(a+b)%p for b in range(q)] for a in range(q)],dtype=np.int64)
        mul=np.array([[(a*b)%p for b in range(q)] for a in range(q)],dtype=np.int64)
    elif q in (4,8):
        n={4:2,8:3}[q]; mod={4:0b111,8:0b1011}[q]
        def pm(a,b):
            r=0
            for i in range(n):
                if (b>>i)&1: r^=a<<i
            for i in range(2*n-2,n-1,-1):
                if (r>>i)&1: r^=mod<<(i-n)
            return r
        add=np.array([[a^b for b in range(q)] for a in range(q)],dtype=np.int64)
        mul=np.array([[pm(a,b) for b in range(q)] for a in range(q)],dtype=np.int64)
    elif q==9:
        # a + b*i, i^2 = -1 (x^2+1 irreducible over F3); encode a+3b
        def dec(x): return x%3, x//3
        def enc(a,b): return (a%3)+3*(b%3)
        add=np.array([[enc(dec(x)[0]+dec(y)[0],dec(x)[1]+dec(y)[1]) for y in range(9)] for x in range(9)],dtype=np.int64)
        mul=np.array([[enc(dec(x)[0]*dec(y)[0]-dec(x)[1]*dec(y)[1],dec(x)[0]*dec(y)[1]+dec(x)[1]*dec(y)[0]) for y in range(9)] for x in range(9)],dtype=np.int64)
    neg=np.array([int(np.where(add[a]==0)[0][0]) for a in range(q)])
    inv=np.array([0]+[int(np.where(mul[a]==1)[0][0]) for a in range(1,q)])
    # field axioms
    for a in range(q):
        for b in range(q):
            assert add[a,b]==add[b,a] and mul[a,b]==mul[b,a]
            for c in range(q):
                assert mul[a,add[b,c]]==add[mul[a,b],mul[a,c]]
                assert mul[a,mul[b,c]]==mul[mul[a,b],c]
    for a in range(1,q): assert mul[a,inv[a]]==1
    return add,mul,neg,inv
