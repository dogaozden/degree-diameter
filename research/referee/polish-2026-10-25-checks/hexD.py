import sys, itertools, random
import numpy as np
sys.path.insert(0,'.')
from gf import diam
TAB={3:(1,1,2),5:(2,1,0),7:(1,1,0),11:(1,1,3),13:(2,1,1)}
def build(q):
    p=q
    vecs=[]
    for v in itertools.product(range(q),repeat=7):
        nz=[x for x in v if x]
        if not nz or nz[0]!=1: continue   # first nonzero = 1
        if (v[0]*v[4]+v[1]*v[5]+v[2]*v[6]-v[3]*v[3])%q==0: vecs.append(v)
    P=np.array(vecs,dtype=np.int64); n=len(P)
    assert n==(q+1)*(q**4+q*q+1)
    def normv(v):
        v=[int(x)%q for x in v]
        for x in v:
            if x:
                iv=pow(x,-1,q); return tuple((iv*y)%q for y in v)
    pid={tuple(v):i for i,v in enumerate(vecs)}
    lines=set()
    pairs=[(1,2,3,4),(5,4,3,2),(2,0,3,5),(6,5,3,0),(0,1,3,6),(4,6,3,1)]
    for i in range(n):
        x=P[i]
        B=(x[0]*P[:,4]+x[4]*P[:,0]+x[1]*P[:,5]+x[5]*P[:,1]+x[2]*P[:,6]+x[6]*P[:,2]-2*x[3]*P[:,3])%q
        ok=(B==0)
        for (a,b,c,d) in pairs:
            pab=x[a]*P[:,b]-x[b]*P[:,a]; pcd=x[c]*P[:,d]-x[d]*P[:,c]
            ok&=((pab-pcd)%q==0)
        ok[i]=False
        nb=np.nonzero(ok)[0]
        assert len(nb)==q*(q+1),(i,len(nb))
        for j in nb:
            if j<i: continue
            y=P[j]
            L=frozenset([i,j]+[pid[normv(x+t*y)] for t in range(1,q)])
            lines.add(L)
    lines=sorted(lines,key=lambda L:sorted(L))
    assert len(lines)==n
    return P,lines
def theoremD(q,ms=(2,),doR=True):
    c,c0,c1=TAB[q]
    P,lines=build(q); n=len(P)
    on=[[] for _ in range(n)]
    for j,L in enumerate(lines):
        for x in L: on[x].append(j)
    vpts=[i for i in range(n) if all(P[i][k]==0 for k in (0,2,3,4,5))]
    assert len(vpts)==q+1
    v=next(j for j,L in enumerate(lines) if set(vpts)==set(L))
    inPi=lambda i,al=0,be=0:(P[i][0]+c*P[i][4]+al*P[i][2]+be*P[i][5])%q==0
    PPi=set(i for i in range(n) if inPi(i))
    S=[j for j,L in enumerate(lines) if all(x in PPi for x in L)]
    assert len(S)==q**3+1 and v in S
    Lv=[j for x in vpts for j in on[x] if j!=v]
    assert len(set(Lv))==q*q+q
    # distance-from-v classification of points
    d3=set(x for j in Lv for x in lines[j])-set(vpts)
    free=set(range(n))-PPi-d3-set(vpts)
    assert len(free)==q**3*(q*q-1)
    # check Lemma 6.1(d)
    assert all((P[i][2]==0 and P[i][5]==0) == (i in d3 or i in vpts) for i in range(n))
    inv=lambda x: pow(int(x),-1,q)
    def nu(i):
        X=P[i]; return ((X[2]*X[3]-X[4]*X[5])*inv(c*X[2]*X[2]+X[5]*X[5]))%q
    def Ffun(al,be):
        G=((c0*al+c1*be)*(al*al+c*be*be)-be**3)%q
        return (G*inv(al*al+c*be*be))%q
    # check G zero free and -c nonsquare
    sq=set((t*t)%q for t in range(1,q))
    assert (-c)%q not in sq
    assert all(((c0*a+c1*b)*(a*a+c*b*b)-b**3)%q for a in range(q) for b in range(q) if (a,b)!=(0,0))
    W=[]; Szcount={}
    for j,L in enumerate(lines):
        if j==v or j in S: continue
        zs=[(al,be) for al in range(q) for be in range(q) if (al,be)!=(0,0) and all(inPi(x,al,be) for x in L)]
        if not zs: continue
        assert len(zs)==1
        al,be=zs[0]; Szcount[zs[0]]=Szcount.get(zs[0],0)+1
        X=[x for x in L if x in PPi]; assert len(X)==1 and X[0] not in vpts
        if nu(X[0])==Ffun(al,be): W.append(j)
    assert all(cnt==q**3 for cnt in Szcount.values()) and len(Szcount)==q*q-1
    cover=[0]*n
    for j in W:
        for x in lines[j]:
            if x in free: cover[x]+=1
    print("q",q,"|W|",len(W),"expected",q*q*(q*q-1),"free cover counts",sorted(set(cover[x] for x in free)),flush=True)
    lev={}
    for x in range(n): lev[('p',x)]=-1
    for j in range(n): lev[('l',j)]=-1
    for x in PPi: lev[('p',x)]=0
    for j in Lv+W: lev[('l',j)]=0
    for j in S: lev[('l',j)]=1
    for x in vpts: lev[('p',x)]=1
    lev[('l',v)]=2
    for m in ms:
        ver={}
        for e,k in lev.items():
            for w in itertools.product(range(m),repeat=k+1): ver[(e,w)]=len(ver)
        bywd={}
        for (e,w),i in ver.items(): bywd.setdefault(e,[]).append(w)
        def comp(w,u): return w[:len(u)]==u if len(w)>=len(u) else u[:len(w)]==w
        edges=[]
        for j,L in enumerate(lines):
            for x in L:
                for w in bywd[('l',j)]:
                    for u in bywd[('p',x)]:
                        if comp(w,u): edges.append((ver[(('p',x),u)],ver[(('l',j),w)]))
        N=len(ver)
        exp=2*(q+1)*(q**4+q*q+1)+(m-1)*(2*q**4+2*q**3+2*q+2+m*(q**3+q+2)+m*m)
        print("  D: m",m,"order",N,"expected",exp,diam(N,edges),flush=True)
        if doR:
            # Theorem R deletion
            Sv=[j for j in S if j!=v]; R=set(random.Random(0).sample(Sv,q))
            dele=set()
            for w in bywd[('l',v)]:
                if w[2]>=1: dele.add(ver[(('l',v),w)])
            for j in Sv:
                if j in R: continue
                for w in bywd[('l',j)]:
                    if w[1]>=1: dele.add(ver[(('l',j),w)])
            assert len(dele)==(m-1)*m*(q**3-q+m)
            keep=[i for i in range(N) if i not in dele]; ren={i:k for k,i in enumerate(keep)}
            E=[(ren[a],ren[b]) for a,b in edges if a in ren and b in ren]
            ptset=set(ver[(e,w)] for (e,w) in ver if e[0]=='p')
            Delta=q+m; deg=[0]*len(keep); 
            for a,b in E: deg[a]+=1; deg[b]+=1
            isP=[keep[k] in ptset for k in range(len(keep))]
            assert sum(isP)==len(keep)-sum(isP)
            # Lemma 7.2 swap completion
            adj=set(E)
            Jp=[k for k in range(len(keep)) if isP[k] for _ in range(Delta-deg[k])]
            Jl=[k for k in range(len(keep)) if not isP[k] for _ in range(Delta-deg[k])]
            assert len(Jp)==len(Jl)
            rr=random.Random(1); rr.shuffle(Jl)
            J=list(zip(Jp,Jl))
            def bad(J):
                from collections import Counter
                C=Counter(J); return [i for i,e in enumerate(J) if e in adj or C[e]>1]
            it=0
            while True:
                B=bad(J)
                if not B: break
                i=B[0]; p0,L0=J[i]
                cur=set(adj)|set(J)
                cand=[k for k,(p1,L1) in enumerate(J) if (p1,L0) not in cur and (p0,L1) not in cur]
                k=rr.choice(cand); p1,L1=J[k]
                J[i]=(p0,L1); J[k]=(p1,L0); it+=1
            E2=E+J
            exp=2*(q+1)*(q**4+q*q+1+(m-1)*(q**3+m+1))
            print("  R: m",m,"order",len(keep),"expected",exp,"swaps",it,diam(len(keep),E2),flush=True)
if __name__=="__main__":
    q=int(sys.argv[1]); ms=tuple(int(x) for x in sys.argv[2].split(','))
    theoremD(q,ms)
