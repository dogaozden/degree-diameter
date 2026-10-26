import sys, hashlib
from collections import defaultdict
def load(fn):
    with open(fn) as f:
        n=int(f.readline())
        adj=[[] for _ in range(n)]
        for line in f:
            p=line.split()
            if len(p)<2: continue
            u,v=int(p[0]),int(p[1]); adj[u].append(v); adj[v].append(u)
    return n,adj
def inv(fn, L=10):
    n,adj=load(fn)
    out=[]
    for s in (0,n//2):  # vertex 0 (side A) and vertex n-1 (side B? use n-1 and n//2 as probes)
        pass
    res=[]
    for s in (0, n-1):
        w=[0]*n; w[s]=1
        prof=[]
        for step in range(L):
            nw=[0]*n
            for u in range(n):
                if w[u]:
                    for v in adj[u]: nw[v]+=w[u]
            w=nw
            prof.append(tuple(sorted(w)))
        res.append(prof)
    # hash the walk profiles
    h=hashlib.sha1(repr(res).encode()).hexdigest()[:12]
    # also number of 4-cycles and 6-cycles via closed walks from vertex 0 not needed
    return h
for fn in sys.argv[1:]:
    print(fn, inv(fn))
