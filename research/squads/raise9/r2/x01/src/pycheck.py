import sys
from collections import deque
P,K,R=101,25,5
N=P*K
def mul(g,h):
    a1,j1=divmod(g,K); a2,j2=divmod(h,K)
    return ((a1+pow(R,j1,P)*a2)%P)*K+(j1+j2)%K
S=[int(x) for x in sys.argv[1:]]
def nbrs(v):
    if v<N: return [N+mul(s,v) for s in S]
    x=v-N
    out=[]
    for s in S:
        # s^{-1} x : find inverse by search table
        out.append(mul(INV[s],x))
    return out
INV={}
for s in S:
    for h in range(N):
        if mul(s,h)==0: INV[s]=h; break
tot=0; ecc=[]
for src in (0,N):
    dist={src:0}; dq=deque([src])
    while dq:
        v=dq.popleft()
        for w in nbrs(v):
            if w not in dist: dist[w]=dist[v]+1; dq.append(w)
    within=sum(1 for d in dist.values() if d<=9)
    ecc.append(max(dist.values())); tot+=2*N-within
    print("src",src,"reached",len(dist),"within9",within,"ecc",max(dist.values()))
print("cost",tot)
