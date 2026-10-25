# Baseline for card c3: joint_cover(F) on 21 opposite flags of H(8), seed 1, and its uncovered totals.
import sys, time, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r3/tools')
import numpy as np
from hexkit import Hex
from collections import Counter
t0 = time.time()
H = Hex(8); N = H.N
K = 21
F = H.random_opposite_flags(K, 1)
print('flags', len(F), 'time', round(time.time() - t0, 1), flush=True)
vp, vl = H.vectors(F)
freedP = {p for p, l in F}; freedL = {l for p, l in F}
cp = Counter(v for u, v in enumerate(vp) if u not in freedP)
cl = Counter(v for L, v in enumerate(vl) if L not in freedL)
mis = sum(abs(cp[v] - cl[v]) for v in set(cp) | set(cl))
left = sum(max(0, cp[v] - cl[v]) for v in set(cp) | set(cl))
print('mismatch', mis, 'leftover points', left, 'distinct point vectors', len(cp), 'distinct line vectors', len(cl), flush=True)
M0 = H.joint_cover(F, 1)
assert len(set(M0.tolist())) == N and all(M0[p] == l for p, l in F)
U0 = H.uncovered(F, M0)
tot0 = sum(a + b for a, b in U0)
print('baseline uncovered total', tot0, 'per pair', U0, 'time', round(time.time() - t0, 1), flush=True)
np.save('/home/user/degree-diameter/research/squads/d10D7-r3/c3/F21.npy', np.array(F, dtype=np.int64))
np.save('/home/user/degree-diameter/research/squads/d10D7-r3/c3/M_base.npy', M0)
