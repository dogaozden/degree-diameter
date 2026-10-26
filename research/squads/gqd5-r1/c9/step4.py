import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from lab import *
S = [int(x) for x in np.load('spread_ls.npy')]
O = [int(x) for x in np.load('ovoid_ls.npy')]
print('ovoid ok', not G.col[np.ix_(O,O)].any(), len(O))
c = 5
R0 = S + [c]
# R2 = ovoid alone (friendly identity H->D) with R0 empty: validity
n,E = graph(R2=O); print('R2=ovoid alone:', bad(n,E))
n,E = graph(R0=S, R2=O); print('R0=spread18 + R2=ovoid, no hubs:', bad(n,E))
# R1 candidates: greedy random small set of points of level 1 (non-friendly): test a few sizes
rng = np.random.default_rng(0)
for k in (1,2,3,4,6):
    res=[]
    for t in range(3):
        R1 = list(rng.choice(NP, k, replace=False))
        n,E = graph(R1=R1); res.append(bad(n,E)['bad'])
    print('R1 random size',k,'alone bad counts', res)
