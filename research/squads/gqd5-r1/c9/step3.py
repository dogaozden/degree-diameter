import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from lab import *
S = [int(x) for x in np.load('spread_ls.npy')]
cnt = G.con[:, S].sum(axis=1)
cands = sorted([l for l in range(NL) if l not in S], key=lambda l: cnt[l])
print('conflict counts of outside lines (min 5 smallest):', [int(cnt[l]) for l in cands[:5]])
c = cands[0]; partners = [s for s in S if G.con[c,s]]
print('c =', c, 'partners in spread', partners)
R = S + [c]
n,E = graph(R0=R); print('R0=spread+c (concurrent pair), no hubs:', bad(n,E), apsp_valid(n,E))
