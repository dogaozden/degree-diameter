"""Slot tables for hub families at q=3 with the 112-point spread freed.
Slot s = fi*5 + i  (fi = index of a freed point p in F, i = level). Side L: vertex (p,i) (point vertex).
Side P: vertex (M(p),i) (line vertex). Writes:
  dist_L.bin / dist_P.bin: 560 x 3640 uint8 distances from each slot vertex to every main vertex (255 = unreachable)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d12D7-r2/c8/src')
from q3lib import *
LP = load_hex(); M = load_phi(); S = load_spread()
F = sorted(set(p for l in S for p in LP[l]))
n = NL * B
E = main_edges(LP, M, set(F))
adj = adjlist(n, E)
def tab(vertex_of):
    out = np.zeros((len(F) * NL, n), dtype=np.uint8)
    for fi, p in enumerate(F):
        for i in range(NL):
            d = dist_from(adj, vertex_of(p, i))
            out[fi * NL + i] = np.array([255 if x < 0 else x for x in d], dtype=np.uint8)
    return out
DL = tab(lambda p, i: ID(p, i))
DP = tab(lambda p, i: ID(N + M[p], i))
DL.tofile(sys.argv[1] + '/dist_L.bin'); DP.tofile(sys.argv[1] + '/dist_P.bin')
with open(sys.argv[1] + '/slots_meta.txt', 'w') as f:
    f.write('%d %d %d\n' % (len(F), NL, n)); f.write(' '.join(map(str, F)) + '\n'); f.write(' '.join(map(str, [M[p] for p in F])) + '\n')
print('tables', DL.shape, DP.shape, 'max finite', DL[DL < 255].max(), DP[DP < 255].max())
