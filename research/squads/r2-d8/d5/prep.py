"""Dump point-point and line-line distance matrices of H(q) (q given) as raw uint8: DP then DL (N*N bytes each)."""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import numpy as np
import gh

q = int(sys.argv[1]) if len(sys.argv) > 1 else 3
H = gh.load(q)
N = H.N
Dm, adj = gh.distances(H)
DP = np.ascontiguousarray(Dm[:N, :N])
DL = np.ascontiguousarray(Dm[N:, N:])
INC = np.ascontiguousarray((Dm[:N, N:] == 1))
np.concatenate([DP.ravel(), DL.ravel()]).astype(np.uint8).tofile(f'/home/user/degree-diameter/research/squads/r2-d8/d5/dist_q{q}.bin')
np.save(f'/home/user/degree-diameter/research/squads/r2-d8/d5/inc_q{q}.npy', INC)
hist = {int(d): int(c) for d, c in zip(*np.unique(DP, return_counts=True))}
histL = {int(d): int(c) for d, c in zip(*np.unique(DL, return_counts=True))}
print('N', N, 'point-point dist hist', hist, 'line-line dist hist', histL, 'max d(point,line)', int(Dm[:N, N:].max()))
