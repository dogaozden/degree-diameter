import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
q, N, L, LP, X = load_hex()
print('q', q, 'N', N, 'L', L, 'LP shape', LP.shape, 'X shape', X.shape, 'X max', X.max(), 'X min', X.min())
gp = load_perm(D+'data/g13o61_pts.bin'); gl = load_perm(D+'data/g13o61_lines.bin')
print('perm sizes', len(gp), len(gl), 'bijective', len(np.unique(gp)) == N, len(np.unique(gl)) == L)
for name, fn in (('pts', D+'og_pts.txt'), ('lines', D+'og_lines.txt')):
    M, E, rep, nb = load_og(fn)
    deg = np.array([len(x) for x in nb])
    print(name, 'M', M, 'E', E, 'deg sum/2', deg.sum()//2, 'deg min/max/avg', deg.min(), deg.max(), deg.mean())
    # check rep is smallest element of its orbit
    perm = gp if name == 'pts' else gl
    n = len(perm)
    ok = 0; orbit_sizes = []
    minrep = np.full(n, -1)
    seen = np.zeros(n, bool); orbit_of = np.full(n, -1)
    orbs = []
    for s in range(n):
        if seen[s]: continue
        cyc = []; x = s
        while not seen[x]:
            seen[x] = True; cyc.append(x); x = perm[x]
        orbs.append(cyc)
    print(name, 'number of orbits', len(orbs), 'sizes', set(len(c) for c in orbs))
    for idx, c in enumerate(orbs):
        for x in c: orbit_of[x] = idx
    omin = {idx: min(c) for idx, c in enumerate(orbs)}
    reps_ok = sum(1 for i in range(M) if omin[orbit_of[rep[i]]] == rep[i])
    print(name, 'rep is min of its orbit for', reps_ok, 'of', M)
    print(name, 'distinct orbits among reps', len(set(orbit_of[rep])))
