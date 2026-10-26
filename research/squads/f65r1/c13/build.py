import itertools, random, sys
from collections import deque
q=7
def norm(v):
    v=[x%q for x in v]
    for x in v:
        if x:
            inv=pow(x,q-2,q)
            return tuple((y*inv)%q for y in v)
    return None
PG=sorted({norm(v) for v in itertools.product(range(q),repeat=3) if any(v)})
PTS=list(itertools.product(range(q),repeat=3))
PID={p:i for i,p in enumerate(PTS)}
def add(a,b,t=1): return tuple((x+t*y)%q for x,y in zip(a,b))
def lines_of_dir(u):
    seen=set(); L=[]
    for x in PTS:
        if x in seen: continue
        line=[add(x,u,t) for t in range(q)]
        for y in line: seen.add(y)
        L.append([PID[y] for y in line])
    return L
def build_lines(S):
    lines=[]
    for u in S:
        lines+=lines_of_dir(u)
    assert len(lines)==343
    return lines
def matching(lines):
    # each point matched to exactly one line containing it; lines matched to one point
    adj=[[] for _ in lines]
    for li,L in enumerate(lines):
        adj[li]=L
    ptl=[None]*343   # point -> line
    lnp=[None]*len(lines)  # line -> point
    def try_(li,vis):
        for p in adj[li]:
            if p in vis: continue
            vis.add(p)
            if ptl[p] is None or try_(ptl[p],vis):
                ptl[p]=li; lnp[li]=p; return True
        return False
    for li in range(len(lines)):
        try_(li,set())
    assert all(x is not None for x in lnp)
    return lnp
def graph(lines, lnp):
    # vertices: points 0..342, blocks 343..685
    E=set()
    for li,L in enumerate(lines):
        for p in L:
            if p!=lnp[li]:
                E.add((p,343+li))
    return sorted(E)
def cost(n_side, E, N):
    adj=[[] for _ in range(N)]
    for a,b in E:
        adj[a].append(b); adj[b].append(a)
    bad=0
    for s in range(343):
        dist=[-1]*N; dist[s]=0; dq=deque([s])
        while dq:
            x=dq.popleft()
            if dist[x]>=4: continue
            for y in adj[x]:
                if dist[y]<0:
                    dist[y]=dist[x]+1; dq.append(y)
        bad+=sum(1 for t in range(343) if dist[t]<0 or dist[t]>4)
    return bad
if __name__=="__main__":
    S=[(0,1,6),(1,3,2),(1,5,5),(1,2,6),(1,3,1),(1,4,5),(1,2,2)]
    lines=build_lines(S)
    lnp=matching(lines)
    E=graph(lines,lnp)
    print("edges",len(E))
    print("cost ordered pairs same-side >4:", cost(343,E,686))
