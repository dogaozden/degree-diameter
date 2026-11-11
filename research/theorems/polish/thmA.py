# Check Theorem A in the normalisation E1: 2 X0 X1 = N(X2,X3), E2: 2 eps X0 X1 = N(X2,X3), N = X2^2 - eps X3^2,
# inside AS(q) = P(W(q),x), x=(1:0:0:0), W(q): u0v1-u1v0+u2v3-u3v2. Builds the copy graph, checks degrees, diameter 4.
import itertools, sys
from collections import deque
def field(q):
    # returns elements list and add/mul/neg/inv for GF(q), q prime or 9
    if q==9:
        els=[(a,b) for a in range(3) for b in range(3)]  # a+b i, i^2=-1
        add=lambda x,y:((x[0]+y[0])%3,(x[1]+y[1])%3)
        mul=lambda x,y:((x[0]*y[0]-x[1]*y[1])%3,(x[0]*y[1]+x[1]*y[0])%3)
        zero,one=(0,0),(1,0)
    else:
        els=list(range(q)); add=lambda x,y:(x+y)%q; mul=lambda x,y:(x*y)%q; zero,one=0,1
    neg={x:[y for y in els if add(x,y)==zero][0] for x in els}
    inv={x:[y for y in els if mul(x,y)==one][0] for x in els if x!=zero}
    return els,add,mul,neg,inv,zero,one
def run(q):
    els,add,mul,neg,inv,zero,one=field(q)
    sq={mul(x,x) for x in els}
    eps=[x for x in els if x not in sq][0]
    two=add(one,one)
    def sub(a,b): return add(a,neg[b])
    def N(b,c): return sub(mul(b,b),mul(eps,mul(c,c)))
    det=lambda w,d: sub(mul(w[0],d[1]),mul(w[1],d[0]))
    pts=[(a,(b,c)) for a in els for b in els for c in els]
    idx={p:i for i,p in enumerate(pts)}
    dirs=[(one,zero)]+[(t,one) for t in els]
    lines=set()
    for (a,w) in pts:
        lines.add(frozenset(idx[(add(a,m),w)] for m in els))  # fibre
        for d in dirs:
            D=det(w,d)
            lines.add(frozenset(idx[(add(a,mul(l,D)),(add(w[0],mul(l,d[0])),add(w[1],mul(l,d[1]))))] for l in els))
    lines=list(lines)
    assert len(lines)==q**2*(q+2), len(lines)
    # E1: 2 a = N(w) ; E2: 2 eps a = N(w)
    E1={idx[(mul(inv[two],N(*w)),w)] for (_,w) in pts}
    E2={idx[(mul(inv[mul(two,eps)],N(*w)),w)] for (_,w) in pts}
    for L in lines:
        assert len(L&E1)+len(L&E2)==2
    common=E1&E2
    assert common=={idx[(zero,(zero,zero))]}
    # build graph: points 0..q^3-1, lines, copies
    P=len(pts); nb=[[] for _ in range(P)]
    Lnb=[]
    for j,L in enumerate(lines):
        Lnb.append(list(L))
        for p in L: nb[p].append(P+j)
    V=P+len(lines); adj=nb+[[] for _ in lines]
    for j,L in enumerate(lines): adj[P+j]=list(L)
    for E in (E1,E2):
        for p in sorted(E):
            c=len(adj); adj.append(list(nb[p]))
            for Lv in nb[p]: adj[Lv].append(c)
    n=len(adj); degs={len(a) for a in adj}
    # diameter by BFS
    diam=0
    for s in range(n):
        dist=[-1]*n; dist[s]=0; dq=deque([s])
        while dq:
            u=dq.popleft()
            for v in adj[u]:
                if dist[v]<0: dist[v]=dist[u]+1; dq.append(v)
        assert min(dist)>=0; diam=max(diam,max(dist))
    print(q,'order',n,'=',2*q*q*(q+2),'degrees',degs,'diam',diam)
for q in [int(a) for a in sys.argv[1:]]: run(q)
