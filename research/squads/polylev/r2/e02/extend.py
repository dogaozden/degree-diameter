"""Greedy maximal extension of a point set inside the H(11) collinearity graph (random order, min-conflict first).
usage: extend.py IN_POINTS OUT_POINTS SEED"""
import sys, numpy as np
inf, outf, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
out = '/home/user/degree-diameter/research/squads/polylev/r2/e02/'
A = np.fromfile(out + 'pts11_nb.bin', dtype=np.int32).reshape(-1, 132)
N = A.shape[0]
S = [int(x) for x in open(inf).read().split()]
inS = np.zeros(N, dtype=bool); inS[S] = True
blocked = np.zeros(N, dtype=bool)
blocked[A[S].ravel()] = True
blocked |= inS
rng = np.random.default_rng(seed)
added = 0
for x in rng.permutation(N):
    if blocked[x]: continue
    inS[x] = True; blocked[x] = True; blocked[A[x]] = True; added += 1
pts = np.nonzero(inS)[0]
open(outf, 'w').write('\n'.join(map(str, pts.tolist())) + '\n')
print('input', len(S), 'added', added, 'total', len(pts))
