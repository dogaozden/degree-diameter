import sys, itertools
sys.path.insert(0,'.')
from gf import make, diam
def norm(F,v):
    # scale so that first nonzero coordinate from the RIGHT is 1
    for i in range(len(v)-1,-1,-1):
        if v[i]:
            iv=F.inv[v[i]]; return tuple(F.M[iv][x] for x in v)
    raise ValueError
def run(q,a,c,rotation=True,link10=True,check_table=True):
    F=make(q); S=[0,1,a,c]; T=[0,1,c]; sig={0:c,c:1,1:0}; siginv={v:k for k,v in sig.items()}
    pts=sorted(set(norm(F,v) for v in itertools.product(range(q),repeat=3) if any(v)))
    lns=pts[:]  # same coordinate set
    assert len(pts)==q*q+q+1
    def inc(p,L): return F.a(F.m(p[0],L[0]),F.m(p[1],L[1]),F.m(p[2],L[2]))==0
    X=lambda t:norm(F,(0,t,1)); P=norm(F,(0,1,0)); A=norm(F,(1,0,0))
    ell=norm(F,(1,0,0)); lam=lambda t:norm(F,(0,1,F.neg[t])); laminf=norm(F,(0,0,1))
    I=set()
    for p in pts:
        for L in lns:
            if inc(p,L): I.add((('p',p),('l',L)))
    for s in S: I.discard((('p',X(s)),('l',lam(s))))
    if rotation:
        for t in T: I.add((('p',X(t)),('l',lam(sig[t]))))
    for s in S:
        for w in range(q): I.add((('H',s),('l',norm(F,(w,1,F.neg[s])))))
        for x in range(q): I.add((('p',norm(F,(x,s,1))),('K',s)))
    I.add((('p',P),('M',0)))
    for t in range(q):
        if t not in T: I.add((('p',X(t)),('M',0)))
    for s in S: I.add((('H',s),('M',0)))
    I.add((('Q',0),('l',laminf)))
    for t in range(q):
        if t not in T: I.add((('Q',0),('l',lam(t))))
    for s in S: I.add((('Q',0),('K',s)))
    I.add((('p',A),('K',a))); I.add((('H',a),('l',ell)))
    if link10:
        for t in T: I.add((('H',t),('K',sig[t])))
    else:
        for t in [0,c]: I.add((('H',t),('K',sig[t])))
    Pv=[('p',p) for p in pts]+[('Q',0)]+[('H',s) for s in S]
    Lv=[('l',L) for L in lns]+[('M',0)]+[('K',s) for s in S]
    idx={v:i for i,v in enumerate(Pv+Lv)}
    G=sorted((idx[x],idx[y]) for x,y in I)
    fill=[]
    for x in range(1,q):
        for y in range(q):
            if y not in S: fill.append((('p',norm(F,(x,y,1))),('l',norm(F,(x,1,F.neg[y])))))
        fill.append((('p',norm(F,(x,1,0))),('l',norm(F,(1,0,F.neg[F.inv[x]])))))
    for e in fill: assert e not in I
    R=G+[(idx[x],idx[y]) for x,y in fill]
    n=len(idx)
    deg={}
    for x,y in I: deg[x]=deg.get(x,0)+1; deg[y]=deg.get(y,0)+1
    nd=sum(1 for v in deg if deg[v]==q+1)
    res=(q,a,c,n,diam(n,G),diam(n,R),"deficient:",nd,"expected",2*(q-1)*(q-3))
    if check_table and rotation and link10:
        nb={}
        for x,y in I: nb.setdefault(x,set()).add(y); nb.setdefault(y,set()).add(x)
        L=lambda u,v,w:('l',norm(F,(u,v,w))); Pt=lambda x,y,z:('p',norm(F,(x,y,z)))
        tab={}
        tab[('Q',0)]={('l',laminf)}|{('l',lam(t)) for t in range(q) if t not in T}|{('K',s) for s in S}
        tab[('H',a)]={L(w,1,F.neg[a]) for w in range(q)}|{('M',0),('l',ell)}
        for t in T: tab[('H',t)]={L(w,1,F.neg[t]) for w in range(q)}|{('M',0),('K',sig[t])}
        tab[('M',0)]={('p',P)}|{('p',X(t)) for t in range(q) if t not in T}|{('H',s) for s in S}
        tab[('K',a)]={Pt(x,a,1) for x in range(q)}|{('Q',0),('p',A)}
        for t in T: tab[('K',t)]={Pt(x,t,1) for x in range(q)}|{('Q',0),('H',siginv[t])}
        tab[('p',A)]={('l',lam(t)) for t in range(q)}|{('l',laminf),('K',a)}
        tab[('p',P)]={('l',ell),('l',laminf)}|{L(1,0,w) for w in range(1,q)}|{('M',0)}
        for t in range(q):
            if t not in S: tab[('p',X(t))]={('l',ell)}|{L(w,1,F.neg[t]) for w in range(q)}|{('M',0)}
        tab[('p',X(a))]={('l',ell)}|{L(w,1,F.neg[a]) for w in range(1,q)}|{('M',0),('K',a)}
        for t in T: tab[('p',X(t))]={('l',ell)}|{L(w,1,F.neg[t]) for w in range(1,q)}|{('l',lam(sig[t])),('K',t)}
        for x in range(1,q):
            for y in range(q):
                tab[Pt(x,y,1)]={L(u,1,F.neg[F.a(F.m(u,x),y)]) for u in range(q)}|{L(1,0,F.neg[x])}|({('K',y)} if y in S else set())
            tab[Pt(x,1,0)]={('l',laminf)}|{L(1,F.neg[x],w) for w in range(q)}
        tab[('l',ell)]={('p',P)}|{('p',X(t)) for t in range(q)}|{('H',a)}
        tab[('l',laminf)]={('p',A)}|{Pt(x,1,0) for x in range(q)}|{('Q',0)}
        for t in range(q):
            if t not in S: tab[('l',lam(t))]={('p',A)}|{Pt(x,t,1) for x in range(q)}|{('Q',0)}
        tab[('l',lam(a))]={('p',A)}|{Pt(x,a,1) for x in range(1,q)}|{('Q',0),('H',a)}
        for t in T: tab[('l',lam(t))]={('p',A)}|{Pt(x,t,1) for x in range(1,q)}|{('p',X(siginv[t])),('H',t)}
        for u in range(1,q):
            for w in range(q):
                mw=F.neg[w]
                tab[L(u,1,w)]={Pt(x,F.sub(F.neg[F.m(u,x)],w),1) for x in range(q)}|{Pt(F.neg[F.inv[u]],1,0)}|({('H',mw)} if mw in S else set())
        for w in range(1,q): tab[L(1,0,w)]={Pt(F.neg[w],y,1) for y in range(q)}|{('p',P)}
        assert set(tab)==set(nb), (len(tab),len(nb))
        bad=[v for v in nb if nb[v]!=tab[v]]
        res=res+("table rows wrong:",len(bad), bad[:3])
    return res
if __name__=="__main__":
    for q in [4,5,7,8,9,11,13]:
        F=make(q)
        pairs=[(a,c) for a in range(2,q) for c in range(2,q) if a!=c]
        import random; random.seed(q)
        sel=pairs if q<=5 else random.sample(pairs,3)
        for a,c in sel:
            print(run(q,a,c),flush=True)
    for q in [5,7]:
        print("no rotation",run(q,2,3,rotation=False,check_table=False))
        print("no link H1-K0",run(q,2,3,link10=False,check_table=False))
