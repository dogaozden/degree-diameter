import sys, itertools, random
sys.path.insert(0,'.')
from gf import make, diam
def build(q):
    F=make(q)
    eps=next(e for e in range(1,q) if F.chi(e)==-1)
    Np=lambda b,c: F.sub(F.m(b,b),F.m(eps,c,c))
    pts=[(a,b,c) for a in range(q) for b in range(q) for c in range(q)]
    pid={p:i for i,p in enumerate(pts)}
    lines=[]
    for b in range(q):
        for c in range(q):
            lines.append(frozenset(pid[(mu,b,c)] for mu in range(q)))
    dirs=[(1,d2) for d2 in range(q)]+[(0,1)]
    seen=set()
    for (a0,b0,c0) in pts:
        for (d1,d2) in dirs:
            rho=F.sub(F.m(b0,d2),F.m(c0,d1))
            L=frozenset(pid[(F.a(a0,F.m(l,rho)),F.a(b0,F.m(l,d1)),F.a(c0,F.m(l,d2)))] for l in range(q))
            if L not in seen: seen.add(L); lines.append(L)
    assert len(lines)==q*q+q*q*(q+1), len(lines)
    # GQ check: each point on q+2 lines, anti-flag axiom (exactly one)
    on=[[] for _ in pts]
    for j,L in enumerate(lines):
        assert len(L)==q
        for p in L: on[p].append(j)
    assert all(len(x)==q+2 for x in on)
    coll=[set() for _ in pts]
    for L in lines:
        for p in L: coll[p]|=L
    random.seed(1)
    for _ in range(300):
        p=random.randrange(len(pts)); j=random.randrange(len(lines))
        if p in lines[j]: continue
        assert len(lines[j]&coll[p])==1
    k1=F.inv[2]; k2=F.inv[F.m(2,eps)]
    E1=[pid[(F.m(k1,Np(b,c)),b,c)] for b in range(q) for c in range(q)]
    E2=[pid[(F.m(k2,Np(b,c)),b,c)] for b in range(q) for c in range(q)]
    w=[0]*len(pts)
    for p in E1+E2: w[p]+=1
    sums=set(sum(w[p] for p in L) for L in lines)
    e=pid[(0,0,0)]
    return F,pts,lines,on,w,sums,e
for q in [3,5,7,9]:
    F,pts,lines,on,w,sums,e=build(q)
    # Corollary 4.2: clones of E1, E2 points (e twice)
    nP=len(pts); nL=len(lines); edges=[]
    for j,L in enumerate(lines):
        for p in L: edges.append((p,nP+j))
    nxt=nP+nL
    for p in range(nP):
        for i in range(w[p]):
            for j in on[p]: edges.append((nxt,nP+j))
            nxt+=1
    print(q,"line sums",sums,"w(e)=",w[e],"max w elsewhere",max(w[p] for p in range(nP) if p!=e),"order",nxt,"expected",2*q*q*(q+2),diam(nxt,edges),flush=True)
