# Incidence graph of the generalized hexagon H(2) (split Cayley hexagon over GF(2)), 63 points + 63 lines.
# Points: singular points of Q: x0x4+x1x5+x2x6+x3^2 = 0 in PG(6,2). Lines: totally singular lines spanned by
# x,y whose Plucker coordinates satisfy Tits' six equations (char-free; signs irrelevant mod 2).
import itertools, sys
def Q(v): return (v[0]*v[4]+v[1]*v[5]+v[2]*v[6]+v[3]) % 2
def B(v,w): return (v[0]*w[4]+v[4]*w[0]+v[1]*w[5]+v[5]*w[1]+v[2]*w[6]+v[6]*w[2]) % 2
vecs=[v for v in itertools.product([0,1],repeat=7) if any(v)]
pts=[v for v in vecs if Q(v)==0]
idx={v:i for i,v in enumerate(pts)}
def add(v,w): return tuple((a+b)%2 for a,b in zip(v,w))
def P(x,y,i,j): return (x[i]*y[j]+x[j]*y[i])%2
lines=set()
for x,y in itertools.combinations(pts,2):
    z=add(x,y)
    if Q(z)!=0 or B(x,y)!=0: continue
    p=lambda i,j: P(x,y,i,j)
    if p(1,2)==p(3,4) and p(5,4)==p(3,2) and p(2,0)==p(3,5) and p(6,5)==p(3,0) and p(0,1)==p(3,6) and p(4,6)==p(3,1):
        lines.add(frozenset([idx[x],idx[y],idx[z]]))
lines=sorted(sorted(l) for l in lines)
L=len(lines)
edges=[]
for j,l in enumerate(lines):
    for i in l: edges.append((i, len(pts)+j))
n=len(pts)+L
# checks
from collections import Counter
deg=Counter()
for a,b in edges: deg[a]+=1; deg[b]+=1
print("points",len(pts),"lines",L,"degrees",set(deg.values()),file=sys.stderr)
adj=[[] for _ in range(n)]
for a,b in edges: adj[a].append(b); adj[b].append(a)
from collections import deque
def bfs(s):
    d=[-1]*n; d[s]=0; q=deque([s])
    while q:
        u=q.popleft()
        for w in adj[u]:
            if d[w]<0: d[w]=d[u]+1; q.append(w)
    return d
diam=max(max(bfs(s)) for s in range(n))
print("n",n,"diameter",diam,file=sys.stderr)
with open(sys.argv[1],"w") as f:
    f.write(f"{n}\n")
    for a,b in edges: f.write(f"{a} {b}\n")
