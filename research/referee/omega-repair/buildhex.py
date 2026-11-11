# H(q) from split octonions: points = <x>, x pure (trace 0), N(x)=0; lines = 2-spaces <x,y> with xy = 0.
# Output: hex_q.npz with pts (N x 7 pure coords (a,u1..u3,v1..v3)), lines (N x (q+1) point indices).
import sys, numpy as np, itertools, time
from octo import Oct
q=int(sys.argv[1]); o=Oct(q); add,mul,neg,inv=o.add,o.mul,o.neg,o.inv
def full(p):   # pure coords -> octonion (a,u,v,-a)
    return [p[0]]+list(p[1:7])+[neg[p[0]]]
def normalize(p):
    p=list(p)
    for c in p:
        if c:
            ic=inv[c]; return tuple(int(mul[ic,x]) for x in p)
    return None
# enumerate normalized pure vectors with N=0
t0=time.time()
pts=[]
for p in itertools.product(range(q),repeat=7):
    if not any(p): continue
    first=next(c for c in p if c)
    if first!=1: continue
    if o.norm(full(p))==0: pts.append(p)
N=len(pts); assert N==(q**6-1)//(q-1), N
idx={p:i for i,p in enumerate(pts)}
# kernel of y -> x*y on pure space
basis=[]
for j in range(7):
    e=[0]*7; e[j]=1; basis.append(full(e))
def kernel(rows_cols):
    # matrix A (8 x 7) given as list of columns; return basis of {c : sum c_j col_j = 0}
    A=[[rows_cols[j][i] for j in range(7)] for i in range(8)]
    piv=[]; r=0
    A=[row[:] for row in A]
    for col in range(7):
        pr=next((i for i in range(r,8) if A[i][col]),None)
        if pr is None: continue
        A[r],A[pr]=A[pr],A[r]
        iv=inv[A[r][col]]; A[r]=[int(mul[iv,x]) for x in A[r]]
        for i in range(8):
            if i!=r and A[i][col]:
                f=A[i][col]; A[i]=[int(add[A[i][k],neg[mul[f,A[r][k]]]]) for k in range(7)]
        piv.append(col); r+=1
    free=[c for c in range(7) if c not in piv]
    ker=[]
    for fc in free:
        v=[0]*7; v[fc]=1
        for i,pc in enumerate(piv): v[pc]=int(neg[A[i][fc]])
        ker.append(v)
    return ker
lineset={}
for i,p in enumerate(pts):
    x=full(p)
    cols=[o.prod(x,e) for e in basis]
    K=kernel(cols)
    assert len(K)==3, (p,len(K))
    # all points of span(K)
    W=set()
    for cs in itertools.product(range(q),repeat=3):
        v=[0]*7
        for c,k in zip(cs,K):
            if c: v=[int(add[v[j],mul[c,k[j]]]) for j in range(7)]
        n=normalize(v)
        if n: W.add(n)
    assert len(W)==q*q+q+1 and p in W
    # check x*y = 0 and y singular for each y in W
    for y in W:
        assert o.norm(full(y))==0
    rest=set(W)-{p}
    while rest:
        y=rest.pop()
        L={p,y}
        for lam in range(1,q):
            v=[int(add[y[j],mul[lam,p[j]]]) for j in range(7)]
            L.add(normalize(v))
        assert len(L)==q+1 and L<= W
        rest-=L
        key=tuple(sorted(idx[z] for z in L))
        lineset[key]=1
lines=sorted(lineset)
assert len(lines)==N, len(lines)
deg=np.zeros(N,int)
for L in lines:
    for z in L: deg[z]+=1
assert (deg==q+1).all()
# products vanish on every line
for L in lines[:2000]:
    for a in L:
        for b in L:
            assert not any(o.prod(full(pts[a]),full(pts[b])))
np.savez("hex_q%d.npz"%q,pts=np.array(pts,dtype=np.int64),lines=np.array(lines,dtype=np.int64))
with open("hex_q%d.txt"%q,"w") as f:
    f.write("%d %d\n"%(q,N))
    for L in lines: f.write(" ".join(map(str,L))+"\n")
print("q=%d: %d points, %d lines, all lines of size q+1, every point on q+1 lines (%.0fs)"%(q,N,len(lines),time.time()-t0))
