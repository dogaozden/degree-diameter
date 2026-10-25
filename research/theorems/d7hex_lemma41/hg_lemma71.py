# Lemma 7.1 check: PG(2,s) incidence graph (s prime) + pendant trees sized as in the proof; same-colour distances <= 6.
import itertools, collections, sys
def pg2(s):
    pts=[]
    for v in itertools.product(range(s),repeat=3):
        if any(v):
            f=next(x for x in v if x); inv=pow(f,s-2,s); w=tuple(x*inv%s for x in v)
            if w not in pts: pts.append(w)
    return pts, [(a,b) for a in range(len(pts)) for b in range(len(pts)) if sum(x*y for x,y in zip(pts[a],pts[b]))%s==0]
def build(s,t,u,K):
    pts,inc=pg2(s); n0=len(pts); assert n0<=K<=n0*(1+t+t*u)
    c=-(-(K-n0)//(1+u)); g=K-n0-c; assert c<=n0*t and g<=u*c
    adj=collections.defaultdict(set); col={}
    for i in range(n0): col[('P',i)]=0; col[('L',i)]=1
    for a,b in inc: adj[('P',a)].add(('L',b)); adj[('L',b)].add(('P',a))
    for side,colr in (('P',0),('L',1)):
        kids=[]
        for i in range(c):                       # c depth-1 children, at most t per core vertex
            par=(side,i//t) if t else None; k=('c',side,i); adj[par].add(k); adj[k].add(par); col[k]=1-colr; kids.append(k)
        for i in range(g):                       # g depth-2 children, at most u per depth-1 vertex
            par=kids[i//u]; k=('g',side,i); adj[par].add(k); adj[k].add(par); col[k]=colr
    deg=max(len(v) for v in adj.values())
    sizes=collections.Counter(col.values())
    worst=0
    for v in col:
        d={v:0}; fr=[v]
        while fr:
            nx=[]
            for x in fr:
                for y in adj[x]:
                    if y not in d: d[y]=d[x]+1; nx.append(y)
            fr=nx
        worst=max(worst,max(d[w] for w in col if col[w]==col[v]))
    return sizes, deg, worst
for (s,t,u,K) in [(2,1,3,35),(2,1,3,20),(3,2,5,169),(3,2,5,100),(5,2,7,527),(5,2,7,300),(2,5,7,287)]:
    sizes,deg,worst=build(s,t,u,K); print(f's={s} t={t} u={u} K={K}: sizes {dict(sizes)}, max degree {deg} (bound {max(s+1+t,u+1)}), max same-colour distance {worst}')
def kappa(d):
    pp=[s for s in range(2,d) if all(s%p for p in range(2,s)) or s in (4,8,9,16)]
    return max((s*s+s+1)*(1+(d-s-1)*d) for s in pp if s+1<=d)
print({d:kappa(d) for d in (3,4,8,9,10,11)})
