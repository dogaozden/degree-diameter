#!/usr/bin/env python3
"""Card c4 (squad round 4): for every outside point y of the 720 set, the set sig(y) of S-orbits (of the group G) that
contain a blocker of y.  Removing a union T of S-orbits frees exactly the points y with sig(y) <= T (subset of T).
Writes sig720.npy (16-bit masks, one per point of H(11), 0 for set points)."""
import sys, os
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L

S = np.loadtxt(os.path.join(HERE, 'init720_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
lab = np.load(os.path.join(HERE, 'lab720.npy'))
labs_S = np.load(os.path.join(HERE, 'labs_S720.npy'))
orb_pos = {int(l): i for i, l in enumerate(labs_S.tolist())}
N = L.N
PJ = L.PJ                      # row y = (J y)^T, B(x, y) = PJ[y] . x  (mod p)
P = L.P
sig = np.zeros(N, np.int64)
inS = np.zeros(N, bool); inS[S] = True
for s in S.tolist():
    z = ((PJ @ P[s]) % 11) == 0            # points y with B(s, y) = 0 (incl. y = s)
    sig[z] |= (1 << orb_pos[int(lab[s])])
sig[inS] = 0
sig[(~inS) & (sig == 0)] = -1              # should not happen
np.save(os.path.join(HERE, 'sig720.npy'), sig)
out = sig[~inS]
print('outside points', out.size, 'distinct signatures', np.unique(out).size, 'min popcount of sig',
      min(bin(v).count('1') for v in np.unique(out).tolist()))
