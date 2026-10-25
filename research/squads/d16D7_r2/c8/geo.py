import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *

def build_PL(LP, N):
    L = LP.shape[0]
    flat = LP.ravel()
    lines_of = np.repeat(np.arange(L), LP.shape[1])
    order = np.argsort(flat, kind='stable')
    PL = lines_of[order].reshape(N, -1)
    return PL

def orbits_of(perm):
    n = len(perm); seen = np.zeros(n, bool); orbit_of = np.full(n, -1, dtype=np.int64); orbs = []
    for s in range(n):
        if seen[s]: continue
        cyc = []; x = s
        while not seen[x]:
            seen[x] = True; cyc.append(x); x = int(perm[x])
        orbit_of[cyc] = len(orbs); orbs.append(cyc)
    return orbit_of, orbs
