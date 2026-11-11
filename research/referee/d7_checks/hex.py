# Independent referee check: build H(q) from the coordinates of D7_HEXAGON.md §1.1 (prime q only)
import itertools, sys, random
import numpy as np
from collections import deque

def build(q):
    pts=[]
    for v in itertools.product(range(q),repeat=7):
        if all(c==0 for c in v): continue
        f=next(c for c in v if c)
        if f!=1: continue
        if (v[0]*v[4]+v[1]*v[5]+v[2]*v[6]-v[3]*v[3])%q==0: pts.append(v)
    P=np.array(pts,dtype=np.int64); N=len(pts)
    idx={tuple(p):i for i,p in enumerate(pts)}
    def norm(v):
        v=[int(c)%q for c in v]
        f=next(c for c in v if c); inv=pow(f,q-2,q)
        return tuple((c*inv)%q for c in v)
    def b(X,Y): # X: (7,), Y: (n,7)
        return (X[0]*Y[:,4]+X[4]*Y[:,0]+X[1]*Y[:,5]+X[5]*Y[:,1]+X[2]*Y[:,6]+X[6]*Y[:,2]-2*X[3]*Y[:,3])%q
    eqs=[((1,2),(3,4)),((5,4),(3,2)),((2,0),(3,5)),((6,5),(3,0)),((0,1),(3,6)),((4,6),(3,1))]
    lines=set()
    for i in range(N):
        x=P[i]; m=np.where(b(x,P)==0)[0]; m=m[m!=i]; Y=P[m]
        ok=np.ones(len(m),bool)
        for (a,c),(d,e) in eqs:
            pac=x[a]*Y[:,c]-x[c]*Y[:,a]; pde=x[d]*Y[:,e]-x[e]*Y[:,d]
            ok&=((pac-pde)%q==0)
        for jj in m[ok]:
            y=P[jj]
            L=frozenset(idx[norm([l*x[k]+mu*y[k] for k in range(7)])] for l in range(q) for mu in range(q) if (l,mu)!=(0,0))
            lines.add(L)
    lines=sorted(lines,key=lambda s:sorted(s))
    return P,pts,idx,lines,norm,b

def incidence(N,lines):
    adj=[[] for _ in range(2*N)]
    for li,L in enumerate(lines):
        for p in L: adj[p].append(N+li); adj[N+li].append(p)
    return adj

def apsp(adj):
    n=len(adj); D=np.full((n,n),99,dtype=np.int8)
    for s in range(n):
        d=D[s]; d[s]=0; dq=deque([s])
        while dq:
            u=dq.popleft()
            for w in adj[u]:
                if d[w]==99: d[w]=d[u]+1; dq.append(w)
    return D

if __name__=="__main__":
    q=int(sys.argv[1])
    P,pts,idx,lines,norm,b=build(q); N=len(pts)
    print("q",q,"points",N,"lines",len(lines),"expected",(q**6-1)//(q-1))
    print("line sizes",set(len(L) for L in lines))
    adj=incidence(N,lines)
    print("degrees",set(len(a) for a in adj))
    D=apsp(adj)
    prof=set()
    for s in range(2*N):
        prof.add(tuple(np.bincount(D[s],minlength=7)[:8]))
    print("distance profiles",prof, "expected", [1]+[(q+1)*q**(i-1) for i in range(1,6)]+[q**5])
    # F4
    bad=0
    for i in range(N):
        bb=b(P[i],P)
        bad+=int(np.sum((bb==0)!=(D[i,:N]<=4)))
    print("F4 violations",bad)
    np.save(f"D{q}.npy",D)
    import pickle; pickle.dump((pts,lines),open(f"H{q}.pkl","wb"))
