"""Long root elations: x -> x + B(x,u)v - B(x,v)u is a collineation of H(q) iff <u,v> is a hexagon line (sampled)."""
import sys, numpy as np, random
sys.path.insert(0,'.')
from geo import Hex
for q in [2,3,4,5]:
    H=Hex(f'hex_q{q}.txt'); F=H.F
    A=np.eye(3,dtype=np.int64); A[0,1]=1
    print(q,'sl3 trans', H.is_coll(H.sl3(A)))
    # siegel with hexagon line axes
    ok=0; tot=0
    for li in random.Random(1).sample(range(H.n), 20):
        u=H.P[H.L[li][0]]; v=H.P[H.L[li][1]]
        tot+=1; ok+=H.is_coll(H.siegel(u,v))
    print(' siegel hexline axis', ok,'/',tot)
    # siegel with non-hexagon t.s. lines: pick two perpendicular points not on a common hex line
    ok=0;tot=0; rng=random.Random(2)
    while tot<20:
        a,b=rng.sample(range(H.n),2)
        if H.B(H.P[a],H.P[b])!=0: continue
        if any(b in H.L[l] for l in H.lines_of[a]): continue
        tot+=1; ok+=H.is_coll(H.siegel(H.P[a],H.P[b]))
    print(' siegel ideal-line axis', ok,'/',tot)
