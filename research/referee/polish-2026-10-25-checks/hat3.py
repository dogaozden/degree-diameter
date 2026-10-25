import sys, itertools
sys.path.insert(0,'.')
from gf import make, diam
from hat4 import norm
def run(q,a,index):
    F=make(q); S=[0,1,a]
    pts=sorted(set(norm(F,v) for v in itertools.product(range(q),repeat=3) if any(v)))
    inc=lambda p,L: F.a(F.m(p[0],L[0]),F.m(p[1],L[1]),F.m(p[2],L[2]))==0
    X=lambda t:norm(F,(0,t,1)); P=norm(F,(0,1,0)); A=norm(F,(1,0,0))
    ell=norm(F,(1,0,0)); lam=lambda t:norm(F,(0,1,F.neg[t])); laminf=norm(F,(0,0,1))
    I=set((('p',p),('l',L)) for p in pts for L in pts if inc(p,L))
    I.discard((('p',X(a)),('l',lam(a))))
    for s in S:
        for w in range(q): I.add((('H',s),('l',norm(F,(w,1,F.neg[s])))))
        for x in range(q): I.add((('p',norm(F,(x,s,1))),('K',s)))
        I.add((('H',s),('M',0))); I.add((('Q',0),('K',s)))
    I.add((('p',P),('M',0))); I.add((('Q',0),('l',laminf)))
    for t in range(2,q): I.add((('p',X(t)),('M',0))); I.add((('Q',0),('l',lam(t))))
    I|={(('p',A),('K',a)),(('H',a),('l',ell)),(('H',0),('K',1)),(('H',1),('K',0))}
    fill=[]
    for x in range(1,q):
        for y in range(q):
            if y not in S: fill.append((('p',norm(F,(x,y,1))),('l',norm(F,(x,F.neg[1],y)))))
    for i in index: fill.append((('p',norm(F,(1,i,0))),('l',norm(F,(1,0,F.neg[i])))))
    for e in fill: assert e not in I
    E=list(I)+fill
    V=sorted(set(x for e in E for x in e),key=str); idx={v:k for k,v in enumerate(V)}
    deg={}
    for x,y in E: deg[x]=deg.get(x,0)+1; deg[y]=deg.get(y,0)+1
    low=sorted(str(v) for v in deg if deg[v]==q+1)
    return len(V),2*(q*q+q+5),diam(len(V),[(idx[x],idx[y]) for x,y in I]),diam(len(V),[(idx[x],idx[y]) for x,y in E]),low
for q in (5,7,9):
    a=2 if q!=9 else 5
    print(q,"printed index set F\\{0,1,a}:",run(q,a,[i for i in range(q) if i not in (0,1,a)]))
    print(q,"index set F*:",run(q,a,list(range(1,q)))[:4])
