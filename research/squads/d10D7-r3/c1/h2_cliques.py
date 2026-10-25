"""Experiment (a): flags of the subhexagon H(2) inside H(8) (points with coordinates in GF(2)).
Enumerates pairwise-opposite (in H(8)) cliques of H(2)-flags and reports mismatch per size."""
import sys, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r3/c1')
from lib import *
from collections import Counter

t0 = time.time()
coords = load_coords()
inH2 = np.all(coords <= 1, axis=1)
cntL = inH2[H.LP].sum(axis=1)
H2L = np.nonzero(cntL == 3)[0]
flags = [(int(p), int(l)) for l in H2L for p in H.LP[l] if inH2[p]]
print('H2 flags', len(flags), flush=True)
fds = [FD(p, l) for p, l in flags]
n = len(fds)
adj = [0] * n
for i in range(n):
    for j in range(n):
        if i != j and opp(fds[i], fds[j]):
            adj[i] |= 1 << j
deg = Counter(bin(a).count('1') for a in adj)
print('opposite-degree distribution in H(2)-flags', sorted(deg.items()), flush=True)
# symmetry check
sym = all(((adj[i] >> j) & 1) == ((adj[j] >> i) & 1) for i in range(n) for j in range(n))
print('symmetric', sym, flush=True)
res = {}
for k in (3, 4):
    cl = cliques(adj, n, k)
    mm = [mismatch([fds[i] for i in c]) for c in cl]
    dist_mm = Counter(mm)
    print('K=%d cliques %d mismatch distribution (lowest 12):' % (k, len(cl)), sorted(dist_mm.items())[:12], flush=True)
    zeros = [c for c, m in zip(cl, mm) if m == 0]
    res[k] = {'cliques': len(cl), 'zeros': len(zeros), 'min': min(mm) if mm else None,
              'example_zero': [flags[i] for i in zeros[0]] if zeros else None}
print('time', round(time.time() - t0, 1), flush=True)
json.dump({'flags': flags, 'res': res}, open('/home/user/degree-diameter/research/squads/d10D7-r3/c1/h2_cliques.json', 'w'))
