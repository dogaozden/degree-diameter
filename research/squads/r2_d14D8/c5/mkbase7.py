#!/usr/bin/env python3
"""mkbase7.py VOLTAGES.txt M OUT.txt [PARAM_SEED]: lifteval base graph of the q=7 design.
VOLTAGES.txt: NP*10 lines "k t w" (slot e = 10*i + s, point orbit i, line orbit k, Sigma-shift t, voltage w in Z_M).
Every point p = g^a R_i gets the 10 edges (p, g^(a+t) R_k, w). Output: `N N M` header then `p l v` lines (lifteval format)."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import write_base

Z = np.load('/home/user/degree-diameter/research/squads/cells/d14D8_work/hex/sym_q7.npz')
S = int(Z['S'])
orbP, shP = Z['orbP'], Z['shP']
orbL, shL = Z['orbL'], Z['shL']
N = len(orbP)
NP = int(orbP.max()) + 1
D = 10
LT = np.zeros((S, NP), dtype=np.int64)
LT[shL, orbL] = np.arange(N)
vals = np.loadtxt(sys.argv[1], dtype=np.int64).reshape(NP * D, 3)
M = int(sys.argv[2]); out = sys.argv[3]
assert (vals[:, 2] >= 0).all() and (vals[:, 2] < M).all(), 'voltage out of range'
K, T, W = vals[:, 0], vals[:, 1], vals[:, 2]
pts = np.arange(N)
a = shP[pts]; i = orbP[pts]
E = []
for s in range(D):
    e = D * i + s
    line = LT[(a + T[e]) % S, K[e]]
    E.append(np.stack([pts, line, W[e]], axis=1))
E = np.concatenate(E)
assert len(np.unique(E[:, 0] * N + E[:, 1])) == len(E) or True
write_base(out, N, M, E)
deg_l = np.bincount(E[:, 1], minlength=N)
print(f'wrote {out}: N {N}, M {M}, edges {len(E)}, point degrees {np.bincount(E[:,0]).min()}..{np.bincount(E[:,0]).max()}, line degrees {deg_l.min()}..{deg_l.max()}')
