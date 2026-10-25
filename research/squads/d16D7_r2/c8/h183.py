import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
from geo import build_PL, orbits_of
q, N, L, LP, X = load_hex()
gp = load_perm(D+'data/g13o61_pts.bin'); gl = load_perm(D+'data/g13o61_lines.bin')
hp = load_perm(D+'data/g13o183_pts.bin'); hl = load_perm(D+'data/g13o183_lines.bin')
print('h bijective', len(np.unique(hp)) == N, len(np.unique(hl)) == L)
# check h^3 == g (or generates same group): compare h^3 with g
h3p = hp[hp[hp]]; h3l = hl[hl[hl]]
print('h^3 == g on points', np.array_equal(h3p, gp), ' on lines', np.array_equal(h3l, gl))
# check h^61 has no fixed points etc: orbit sizes of h
op, orbs_hp = orbits_of(hp); ol, orbs_hl = orbits_of(hl)
from collections import Counter
print('h point orbit sizes', Counter(len(c) for c in orbs_hp), 'line orbit sizes', Counter(len(c) for c in orbs_hl))
# collineation check: h maps lines to lines
key = np.sort(LP, axis=1)
kv = {tuple(r): i for i, r in enumerate(map(tuple, key))}
img = np.sort(hp[LP], axis=1)
ok = all(tuple(r) in kv for r in map(tuple, img[:20000]))
print('h maps first 20000 lines onto lines:', ok)
np.save('h_orbit_pts.npy', op); np.save('h_orbit_lines.npy', ol)
