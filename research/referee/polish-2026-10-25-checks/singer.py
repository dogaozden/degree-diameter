import sys, itertools, random
sys.path.insert(0,'.')
from gf import diam
def polymulmod(a,b,mod,p):
    k=len(mod)  # mod: monic degree k given by coeffs c0..c_{k-1} of x^k = -(...)? use x^k = sum mod[i] x^i
    r=[0]*(2*k)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    for d in range(2*k-1,k-1,-1):
        c=r[d]; r[d]=0
        if c:
            for i,ci in enumerate(mod): r[d-k+i]=(r[d-k+i]+c*ci)%p
    return tuple(r[:k])
def field(p,k=4):
    n=p**k
    for mod in itertools.product(range(p),repeat=k):
        if mod[0]==0: continue
        # test x primitive
        x=tuple([0,1]+[0]*(k-2)); cur=tuple([1]+[0]*(k-1)); seen={}
        ok=True
        for i in range(n-1):
            if cur in seen: ok=False;break
            seen[cur]=i; cur=polymulmod(cur,x,list(mod),p)
        if ok and cur==tuple([1]+[0]*(k-1)) and len(seen)==n-1:
            return mod,seen
    raise ValueError
def run(q,extra_e=0):
    p=q; mod,log=field(p)
    N=q**4-1; exp={v:k for k,v in log.items()}
    zero=(0,0,0,0)
    def add(u,v): return tuple((a+b)%p for a,b in zip(u,v))
    def mul(u,v):
        if u==zero or v==zero: return zero
        return exp[(log[u]+log[v])%N]
    def pw(u,e):
        if u==zero: return zero
        return exp[(log[u]*e)%N]
    g=lambda i: exp[i%N]
    def tr(u):  # Tr_{E/F}
        s=zero
        for j in range(4): s=add(s,pw(u,q**j))
        assert s[1:]==(0,0,0); return s[0]
    bar=lambda u: pw(u,q*q)
    d=g((q*q+1)//2)
    delta0=mul(d,g((q*q+1)*extra_e))  # d*h^e
    npt=(q+1)*(q*q+1)
    # points: indices i mod npt ; vector of point i = g^i
    ptidx={}
    for i in range(N):
        v=g(i); ptidx[v]=i%npt
    b=lambda y,z: tr(mul(delta0,mul(y,bar(z))))
    # lines of PG(3,q): spans
    def span_pts(y,z):
        s=set()
        for t in range(q):
            s.add(ptidx[add(y,tuple((t*c)%p for c in z))])
        s.add(ptidx[z]); return frozenset(s)
    alllines=set(); tilines=set()
    reps=[g(i) for i in range(npt)]
    for i in range(npt):
        for j in range(i+1,npt):
            L=span_pts(reps[i],reps[j])
            if L in alllines: continue
            alllines.add(L)
            if b(reps[i],reps[j])==0: tilines.add(L)
    assert len(alllines)==(q*q+1)*(q*q+q+1) and len(tilines)==(q+1)*(q*q+1),(len(alllines),len(tilines))
    cls=lambda i: i%(q+1)
    # (a)
    amax=max(sum(1 for x in L if cls(x)==a) for L in alllines for a in range(q+1))
    good=sorted((a,bb) for a in range(q+1) for bb in range(a+1,q+1) if all(sum(1 for x in L if cls(x) in (a,bb))==2 for L in tilines))
    return amax,good,tilines,npt,cls,reps,ptidx,g,add,mul
for q in [3,5,7]:
    amax,good,tilines,npt,cls,reps,ptidx,g,add,mul=run(q)
    print("q",q,"max |L cap C_a| over all lines:",amax,"2-ovoid pairs:",good,"expected",[(a,q-a) for a in range((q+1)//2)])
    if q<=5:
        amax2,good2,*_=run(q,extra_e=1)
        print("   form d*h (e=1): pairs",good2,"predicted a+b = -3 mod q+1:",[(a,(-3-a)%(q+1)) for a in range(q+1) if a<(-3-a)%(q+1)])
    if q in (3,5):
        # Corollary 5.2
        O=[i for i in range(npt) if cls(i) in (0,q)]
        spread=[frozenset((i+(q*q+1)*j)%npt for j in range(q+1)) for i in range(q*q+1)]
        assert all(L in tilines for L in spread)
        lines=sorted(tilines,key=lambda L:sorted(L)); lid={L:j for j,L in enumerate(lines)}
        on=[[] for _ in range(npt)]
        for j,L in enumerate(lines):
            for x in L: on[x].append(j)
        nP=npt; nL=len(lines); edges=[(x,nP+j) for j,L in enumerate(lines) for x in L]
        nxt=nP+nL; clones=[]
        for o in O:
            for j in on[o]: edges.append((nxt,nP+j))
            clones.append(nxt); nxt+=1
        shadows=[]
        for L in spread:
            for r in range(2):
                for x in L: edges.append((x,nxt))
                shadows.append(nxt); nxt+=1
        print("   Cor C1:",nxt,"expected",2*(q*q+1)*(q+3),diam(nxt,edges))
        bsz=len(shadows); extra=[]
        for i,cv in enumerate(clones):
            for j in (2*i,2*i+1): extra.append((cv,shadows[j%bsz]))
        assert len(set(extra))==len(extra)
        E2=edges+extra
        print("   regular completion:",diam(nxt,E2),"multi-edges:",len(E2)-len(set(E2)))
