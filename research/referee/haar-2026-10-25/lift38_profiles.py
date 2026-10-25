# Referee check: rebuild the (3,8) lift and compare BFS distance profiles within each colour class (not Haar if they differ).
from collections import deque, Counter
p, M, m = 3, (0, 2, 1, 0), 8
base = [(0,2,(0,0,0)),(0,2,(2,0,3)),(0,3,(0,0,0)),(1,2,(0,0,0)),(1,3,(1,1,3)),(1,3,(1,1,2))]
def mm(A,B): return ((A[0]*B[0]+A[1]*B[2])%p,(A[0]*B[1]+A[1]*B[3])%p,(A[2]*B[0]+A[3]*B[2])%p,(A[2]*B[1]+A[3]*B[3])%p)
P=[(1,0,0,1)]
for _ in range(m): P.append(mm(P[-1],M))
print('M^4 =', P[4], 'M^8 =', P[8])
def mv(A,v): return ((A[0]*v[0]+A[1]*v[1])%p,(A[2]*v[0]+A[3]*v[1])%p)
G=[(x,y,j) for x in range(p) for y in range(p) for j in range(m)]
gi={g:i for i,g in enumerate(G)}
def mul(g,h):
    v=mv(P[g[2]],h[:2]); return ((g[0]+v[0])%p,(g[1]+v[1])%p,(g[2]+h[2])%m)
n=len(G); N=4*n
adj=[[] for _ in range(N)]
for u,w,al in base:
    for g in G:
        a=u*n+gi[g]; b=w*n+gi[mul(g,al)]
        adj[a].append(b); adj[b].append(a)
print('degrees', Counter(len(a) for a in adj), 'simple', all(len(set(a))==len(a) for a in adj))
def prof(s):
    d=[-1]*N; d[s]=0; q=deque([s])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if d[y]<0: d[y]=d[x]+1; q.append(y)
    return tuple(sorted(Counter(d).items()))
profs={}
for v in range(N):
    profs.setdefault((v//n in (0,1)), Counter())[prof(v)]+=1
for side,c in profs.items():
    print('side', 'P(0,1)' if side else 'L(2,3)', 'distinct distance profiles:', len(c))
    for pr,cnt in c.items(): print('   ', cnt, pr)
# girth & number of shortest cycles through each vertex
