import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d12D7-r2/c8/src')
from q3lib import *
LP = load_hex(); M = load_phi(); S = load_spread()
F = set(p for l in S for p in LP[l])
print('freed', len(F))
n = NL * B
E = main_edges(LP, M, set())
write_edges('/home/user/degree-diameter/research/squads/d12D7-r2/c8/main_nofree.edges', n, E)
E2 = main_edges(LP, M, F)
write_edges('/home/user/degree-diameter/research/squads/d12D7-r2/c8/main_free112.edges', n, E2)
print('edges full', len(E), 'freed', len(E2))
adj = adjlist(n, E2)
degs = [len(a) for a in adj]
print('degree histogram', {d: degs.count(d) for d in set(degs)})
