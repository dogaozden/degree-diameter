import sys, itertools, random
sys.path.insert(0,'.')
from gf import make, diam
from hat4 import norm
def run(q,seed):
    F=make(q); rnd=random.Random(seed)
    pts=sorted(set(norm(F,v) for v in itertools.product(range(q),repeat=3) if any(v)))
    inc=lambda p,L: F.a(F.m(p[0],L[0]),F.m(p[1],L[1]),F.m(p[2],L[2]))==0
    ell=rnd.choice(pts); A=rnd.choice([p for p in pts if not inc(p,ell)])
    onl=[p for p in pts if inc(p,ell)]
    X=dict(zip(['0','1','a','c'],rnd.sample(onl,4)))
    def join(p,r):
        for L in pts:
            if inc(p,L) and inc(r,L): return L
    lam={s:join(A,X[s]) for s in X}
    T=['0','1','c']; sig={'0':'c','c':'1','1':'0'}
    I=set((('p',p),('l',L)) for p in pts for L in pts if inc(p,L))
    for s in X: I.discard((('p',X[s]),('l',lam[s])))
    for t in T: I.add((('p',X[t]),('l',lam[sig[t]])))
    for s in X:
        for L in pts:
            if inc(X[s],L) and L!=ell: I.add((('H',s),('l',L)))
        for p in pts:
            if inc(p,lam[s]) and p!=A: I.add((('p',p),('K',s)))
        I.add((('H',s),('M',0))); I.add((('Q',0),('K',s)))
    for p in onl:
        if p not in [X[t] for t in T]: I.add((('p',p),('M',0)))
    for L in pts:
        if inc(A,L) and L not in [lam[t] for t in T]: I.add((('Q',0),('l',L)))
    I.add((('p',A),('K','a'))); I.add((('H','a'),('l',ell)))
    for t in T: I.add((('H',t),('K',sig[t])))
    V=sorted(set(x for e in I for x in e),key=str); idx={v:i for i,v in enumerate(V)}
    return q,len(V),2*(q*q+q+6),diam(len(V),[(idx[a],idx[b]) for a,b in I])
for q in (3,4,5,7):
    for seed in range(3): print(run(q,seed))
