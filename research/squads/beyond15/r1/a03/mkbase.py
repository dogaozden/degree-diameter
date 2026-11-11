import sys
from collections import deque
# Tutte 8-cage (30 vertices) via LCF [-13,-9,7,-7,9,13]^5, relabelled: even -> 0..14, odd -> 15..29
lcf = [-13,-9,7,-7,9,13]*5
n = 30
adj = {i:set() for i in range(n)}
for i in range(n):
    adj[i].add((i+1)%n); adj[(i+1)%n].add(i)
for i in range(n):
    j = (i+lcf[i]) % n
    adj[i].add(j); adj[j].add(i)
assert all(len(adj[i])==3 for i in range(n)), "not cubic"
assert all(j%2!=i%2 for i in range(n) for j in adj[i]), "not bipartite"
def lab(v): return v//2 if v%2==0 else 15+v//2
edges=set()
for i in range(n):
    for j in adj[i]:
        if i<j: edges.add((min(lab(i),lab(j)),max(lab(i),lab(j))))
# girth check
g=99
for s in range(n):
    d={s:0}; par={s:-1}; q=deque([s])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if y not in d: d[y]=d[x]+1; par[y]=x; q.append(y)
            elif par[x]!=y: g=min(g,d[x]+d[y]+1)
print("girth",g, "edges", len(edges), file=sys.stderr)
with open("tutte8.txt","w") as f:
    f.write(f"{n}\n")
    for u,v in sorted(edges): f.write(f"{u} {v}\n")
