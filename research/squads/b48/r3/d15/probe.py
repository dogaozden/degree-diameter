import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/b48/r3/d15')
import numpy as np, random
from coset import *
M,m,k,r = 9944, 2486, 4, 241
mul = make_mul(m,k,r)
subs = subgroups4(M, mul)
print("subgroups of order 4:", len(subs))
rng = random.Random(5)
sets=[set(s) for s in subs]
cnt=0
for t in range(400):
    a=rng.randrange(len(subs)); b=rng.randrange(len(subs))
    if a==b or (sets[a]&sets[b])!={0}: continue
    nbr,idH,idK,NL = build_nbr(M,mul,subs[a],subs[b])
    d0=bfs(nbr,0); d1=bfs(nbr,NL)
    reach0=(d0>=0).sum(); mx=max(d0.max(),d1.max())
    hist=np.bincount(d0[d0>=0])
    print(a,b,"reach",reach0,"of",nbr.shape[0],"ecc0",d0.max(),"ecc_R",d1.max(), "hist",hist.tolist())
    cnt+=1
    if cnt>=6: break
