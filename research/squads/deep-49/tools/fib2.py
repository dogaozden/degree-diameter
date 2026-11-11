import sys, numpy as np
from collections import Counter
sys.path.insert(0,'.')
from meta import table, inv
p,k,r=map(int,sys.argv[1:4]); S=list(map(int,sys.argv[4:8]))
MT=table(p,k,r); I=inv(MT)
for side in 'AB':
    T=sorted({int(MT[s,I[t]]) if side=='A' else int(MT[I[s],t]) for s in S for t in S})
    X=sorted({int(MT[a,b]) for a in T for b in T})
    # multiplicity of each element in X.X (products, not words)
    cnt=Counter(int(MT[a,b]) for a in X for b in X)
    xf=Counter(x//p for x in X)
    print(side,"|T|",len(T),"|X|",len(X),"X fibre sizes",[xf[t] for t in range(k)])
    miss=[g for g in range(p*k) if cnt[g]==0]
    print(" missing",[(g%p,g//p) for g in miss])
    for j in sorted({g//p for g in miss}|{0,1}):
        mult=[cnt[a+p*j] for a in range(p)]
        print("  fibre",j,"products",sum(mult),"mult hist",sorted(Counter(mult).items())[:12])
