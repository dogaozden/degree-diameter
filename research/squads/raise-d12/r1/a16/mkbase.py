import itertools, collections, sys
q=3
pts=[]
for v in itertools.product(range(q),repeat=4):
    if any(v):
        f=next(x for x in v if x)
        if f==1: pts.append(v)
assert len(pts)==40
def B(x,y): return (x[0]*y[1]-x[1]*y[0]+x[2]*y[3]-x[3]*y[2])%q
def norm(v):
    f=next(x for x in v if x)
    inv=1 if f==1 else 2
    return tuple((x*inv)%q for x in v)
idx={p:i for i,p in enumerate(pts)}
lines=set()
for i,p in enumerate(pts):
    for j,r in enumerate(pts):
        if j<=i or B(p,r)!=0: continue
        L=set()
        for a in range(q):
            for b in range(q):
                if a==0 and b==0: continue
                v=tuple((a*p[t]+b*r[t])%q for t in range(4))
                L.add(idx[norm(v)])
        lines.add(frozenset(L))
lines=sorted(sorted(l) for l in lines)
assert len(lines)==40 and all(len(l)==4 for l in lines), len(lines)
edges=[]
for li,L in enumerate(lines):
    for p in L: edges.append((p,40+li))
adj=collections.defaultdict(list)
for u,v in edges: adj[u].append(v); adj[v].append(u)
assert all(len(adj[x])==4 for x in range(80))
# girth and diameter
def bfs(s):
    d={s:0}; Q=collections.deque([s])
    while Q:
        x=Q.popleft()
        for y in adj[x]:
            if y not in d: d[y]=d[x]+1; Q.append(y)
    return d
diam=max(max(bfs(s).values()) for s in range(80))
girth=10**9
for s in range(80):
    d={s:0}; par={s:-1}; Q=collections.deque([s])
    while Q:
        x=Q.popleft()
        for y in adj[x]:
            if y==par[x]: continue
            if y in d: girth=min(girth,d[x]+d[y]+1)
            else: d[y]=d[x]+1; par[y]=x; Q.append(y)
print("vertices",80,"edges",len(edges),"diam",diam,"girth",girth)
with open("base.txt","w") as f:
    f.write("80 %d\n"%len(edges))
    for u,v in edges: f.write("%d %d\n"%(u,v))
