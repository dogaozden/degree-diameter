# Lemma 4.4 at q = 7, independently: for random collineations h of H(7) without fixed points,
# d_c = dim ker(h + h^-1 - c) over F_7, the bound, and the exact |Perp(h)| = #{s : B(s, h s) = 0}.
import numpy as np, random, sys, math
from collin import Hex
q=7; H=Hex(q); R=random.Random(int(sys.argv[2]) if len(sys.argv)>2 else 11)
P=H.pts
def Bvec(X,Y):  # polar form, rows
    r=(-2*X[:,0]*Y[:,0] - (X[:,1:4]*Y[:,4:7]).sum(1) - (Y[:,1:4]*X[:,4:7]).sum(1))%q
    return r
# 1. perpendicular <=> hexagon distance <= 4, from 300 random points (BFS in the incidence graph)
N=H.N
def dist_from(p):
    import collections
    d={('p',p):0}; fr=[('p',p)]
    for r in range(1,7):
        nf=[]
        for (t,x) in fr:
            nb=[('l',l) for l in H.ptlines[x]] if t=='p' else [('p',z) for z in H.lines[x]]
            for y in nb:
                if y not in d: d[y]=r; nf.append(y)
        fr=nf
    return np.array([d[('p',z)] for z in range(N)])
bad=0
for _ in range(30):
    p=R.randrange(N); D=dist_from(p)
    perp=(Bvec(np.repeat(P[p:p+1],N,0),P)==0)
    bad+=int(((D<=4)!=perp).sum())
print("perpendicular <=> distance <= 4 in I: mismatches over 30 sources x %d points: %d"%(N,bad))
def rank_mod(A):
    A=[[int(x)%q for x in row] for row in A]; r=0; n=len(A); m=len(A[0])
    for c in range(m):
        pr=next((i for i in range(r,n) if A[i][c]),None)
        if pr is None: continue
        A[r],A[pr]=A[pr],A[r]; iv=pow(A[r][c],q-2,q); A[r]=[x*iv%q for x in A[r]]
        for i in range(n):
            if i!=r and A[i][c]:
                f=A[i][c]; A[i]=[(A[i][k]-f*A[r][k])%q for k in range(m)]
        r+=1
    return r
def inv_mod(M):
    n=7; A=[list(map(int,M[i]))+[int(i==j) for j in range(n)] for i in range(n)]
    for c in range(n):
        pr=next(i for i in range(c,n) if A[i][c]%q)
        A[c],A[pr]=A[pr],A[c]; iv=pow(A[c][c],q-2,q); A[c]=[x*iv%q for x in A[c]]
        for i in range(n):
            if i!=c and A[i][c]:
                f=A[i][c]; A[i]=[(A[i][k]-f*A[c][k])%q for k in range(2*n)]
    return [row[n:] for row in A]
bound=(q**5-1)//(q-1)+q**3.5+q**3+(q-2)*q**1.5
print("universal bound at q=7: %.2f"%bound)
nf=0; maxd=0; maxsum=0; mingap=1e9; perps={}; pats={}
trials=int(sys.argv[1]) if len(sys.argv)>1 else 200
for _ in range(trials):
    M,(pp,lp)=H.random_collineation(R,nfac=R.choice([2,3,4,6,8]))
    if (pp==np.arange(N)).any(): continue
    nf+=1
    Mi=inv_mod(M)
    ds=[]
    for c in range(q):
        A=[[(M[i][j]+Mi[i][j]-(c if i==j else 0))%q for j in range(7)] for i in range(7)]
        ds.append(7-rank_mod(A))
    maxd=max(maxd,max(ds)); maxsum=max(maxsum,sum(ds))
    hb=q**1.5*sum(q**(d/2) for d in ds)+(q**5-1)/(q-1)
    hP=np.array(M)@P.T%q
    perp=int((Bvec(P,hP.T)==0).sum())
    mingap=min(mingap,hb-perp)
    perps[perp]=perps.get(perp,0)+1
    pats[tuple(sorted([d for d in ds if d],reverse=True))]=pats.get(tuple(sorted([d for d in ds if d],reverse=True)),0)+1
print("fixed-point-free elements sampled: %d of %d"%(nf,trials))
print("max d_c = %d (claim <= 4), max sum d_c = %d (<= 7), min(per-element bound - |Perp|) = %.1f"%(maxd,maxsum,mingap))
print("|Perp(h)| values:",perps,"  max = %d (universal bound %d)"%(max(perps),int(bound)))
print("nonzero kernel patterns:",pats)
