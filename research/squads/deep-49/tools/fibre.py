"""Fibre analysis of Haar sets in Z_p x|_r Z_k (affine group x -> r^j x + a).
For S (list of element indices a + p*j), side A uses T = S S^-1, side B uses T = S^-1 S.
Counts, per fibre j of Z_k: walks of length 4 in T (all 13^4 words, multiplicity), distinct formal words
(polynomials in a1,a2,a3 with coefficients in Z[x]/(x^k-1) -- computed exactly as integer vectors), and
distinct elements reached for the given a."""
import sys, itertools, numpy as np
from collections import defaultdict
def analyse(p,k,r,S,side):
    els=[(x%p, x//p) for x in S]
    # formal: element = (vector over basis (a_i * x^t), j). Represent a-part as tuple of k*len(S) ints: coef of a_i x^t
    nS=len(S)
    def fmul(A,B):
        (va,ja),(vb,jb)=A,B
        v=list(va)
        for i in range(nS):
            for t in range(k):
                c=vb[i*k+t]
                if c: v[i*k+(t+ja)%k]+=c
        return (tuple(v),(ja+jb)%k)
    def finv(A):
        va,ja=A; jn=(-ja)%k
        v=[0]*(nS*k)
        for i in range(nS):
            for t in range(k):
                c=va[i*k+t]
                if c: v[i*k+(t+jn)%k]-=c
        return (tuple(v),jn)
    gen=[]
    for i,(a,j) in enumerate(els):
        v=[0]*(nS*k); v[i*k]=1
        if i==0: v[0]=0   # S contains e = (0,0): a_0 = 0
        gen.append((tuple(v),j))
    if side=='A': T={fmul(s,finv(t)) for s in gen for t in gen}
    else: T={fmul(finv(s),t) for s in gen for t in gen}
    T=list(T)
    # numeric
    rp=[pow(r,t,p) for t in range(k)]
    avals=[a for (a,j) in els]
    def num(F):
        v,j=F; return (sum(c*avals[i]*rp[t] for i in range(nS) for t in range(k) for c in [v[i*k+t]] if c)%p, j)
    level={((0,)*(nS*k),0)}; allf=set(level)
    for _ in range(4):
        level={fmul(A,t) for A in level for t in T}; allf|=level
    W=defaultdict(int); E=defaultdict(set)
    for F in allf:
        W[F[1]]+=1; E[F[1]].add(num(F)[0])
    return {j:(W[j],len(E[j])) for j in range(k)}
if __name__=="__main__":
    p,k,r=map(int,sys.argv[1:4]); S=list(map(int,sys.argv[4:8]))
    for side in 'AB':
        res=analyse(p,k,r,S,side)
        print(side,"fibre j: formal-distinct/reached (of %d)"%p)
        print(" ".join(f"{j}:{res[j][0]}/{res[j][1]}" for j in range(k)))
