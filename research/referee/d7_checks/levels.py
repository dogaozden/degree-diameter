# Theorem A with random bijections and types; Remark 4.2 "only if" by BFS in the two-level graph (multi-edge paths included)
import sys, random, pickle
import numpy as np
from collections import deque
q=3
pts,lines=pickle.load(open(f"H{q}.pkl","rb")); N=len(pts)
spread,spreadpts,ell=pickle.load(open(f"sets{q}.pkl","rb"))
inc=[[] for _ in range(2*N)]
for li,L in enumerate(lines):
    for p in L: inc[p].append(N+li); inc[N+li].append(p)
def ecc_all(adj):
    n=len(adj); worst=0; far=0
    for s in range(n):
        d=[-1]*n; d[s]=0; dq=deque([s])
        while dq:
            u=dq.popleft()
            for w in adj[u]:
                if d[w]<0: d[w]=d[u]+1; dq.append(w)
        if min(d)<0: return None,None
        worst=max(worst,max(d)); far+=sum(1 for x in d if x>7)
    return worst,far
def level_graph(types,r,rng,freed=None):
    L=2*r+1; n=L*2*N; adj=[[] for _ in range(n)]
    V=lambda e,j: j*2*N+e
    for j in range(L):
        for e in range(2*N):
            for w in inc[e]: adj[V(e,j)].append(V(w,j))
    for j in range(L):
        for k in range(1,r+1):
            jj=(j+k)%L
            A=list(range(N)) if types[j]=='H' else list(range(N,2*N))
            B=list(range(N,2*N)) if types[jj]=='H' else list(range(N))
            Bp=B[:]; rng.shuffle(Bp)
            for a,b in zip(A,Bp):
                adj[V(a,j)].append(V(b,jj)); adj[V(b,jj)].append(V(a,j))
    return adj
rng=random.Random(5)
for types,r in (("HHH",1),("HDH",1),("HDHDH",2)):
    adj=level_graph(types,r,rng)
    degs={len(a) for a in adj}
    print("Theorem A",types,"n",len(adj),"degrees",degs,"(diameter, pairs>7)",ecc_all(adj))
# Remark 4.2: two levels H -> D, friendly id, freed set = spread points + one turning point; BFS in the 2-level graph
def two_level(F):
    n=4*N; adj=[[] for _ in range(n)]
    for j in (0,1):
        for e in range(2*N):
            for w in inc[e]: adj[j*2*N+e].append(j*2*N+w)
    for a in range(N):
        if a in F: continue
        adj[a].append(2*N+a); adj[2*N+a].append(a)   # point a in level 0 (H: A) to point a in level 1 (D: B)
    return adj
F=set(spreadpts)
print("two-level H->D, spread points freed:",ecc_all(two_level(F)))
ptl=[[] for _ in range(N)]
for li,L in enumerate(lines):
    for p in L: ptl[p].append(li)
# add a point collinear with a spread point off its spread line -> turning
p0=spreadpts[0]; sl=[l for l in ptl[p0] if l in set(spread)][0]
other=[l for l in ptl[p0] if l!=sl][0]; extra=[x for x in lines[other] if x!=p0][0]
print("two-level, spread points + one turning point:",ecc_all(two_level(F|{extra})))
