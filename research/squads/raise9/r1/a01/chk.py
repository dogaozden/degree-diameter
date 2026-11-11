import numpy as np, sys, random
N=int(sys.argv[1]); fn=sys.argv[2]
with open(fn,'rb') as f:
    n=np.frombuffer(f.read(4),dtype=np.int32)[0]
    T=np.frombuffer(f.read(),dtype=np.uint16).reshape(n,n)
assert n==N
# associativity spot check
rng=np.random.default_rng(1)
for _ in range(2000):
    a,b,c=rng.integers(0,N,3)
    assert T[T[a,b],c]==T[a,T[b,c]]
print("assoc ok; row0 identity:", (T[0]==np.arange(N)).all(), "col0:", (T[:,0]==np.arange(N)).all())
inv=np.array([int(np.where(T[g]==0)[0][0]) for g in range(N)])
def cost(S,D=9):
    res=0
    for src in (0,N):
        dist=-np.ones(2*N,dtype=int); dist[src]=0; front=[src]
        for lev in range(1,D+1):
            nxt=[]
            for v in front:
                if v<N: ws=[T[s,v]+N for s in S]
                else: ws=[T[inv[s],v-N] for s in S]
                for w in ws:
                    if dist[w]<0: dist[w]=lev; nxt.append(w)
            front=nxt
        res+=int((dist<0).sum())
    return res
for _ in range(3):
    S=[0]+random.sample(range(1,N),3)
    print(S, cost(S))
