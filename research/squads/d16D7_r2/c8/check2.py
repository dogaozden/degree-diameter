import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
q, N, L, LP, X = load_hex()
gp = load_perm(D+'data/g13o61_pts.bin'); gl = load_perm(D+'data/g13o61_lines.bin')
# point collinearity: pairs on a common line
pairs = set()
for l in range(L):
    pts = LP[l]
    for i in range(14):
        for j in range(i+1, 14):
            a, b = pts[i], pts[j]
            pairs.add((min(a,b), max(a,b)))
print('collinear point pairs', len(pairs), 'per point', 2*len(pairs)/N)
# check each point on 14 lines
cnt = np.bincount(LP.ravel(), minlength=N)
print('lines per point', np.unique(cnt, return_counts=True))
# orbit graph from geometry for points
M, E, rep, nb = load_og(D+'og_pts.txt')
orbit_of = np.full(N, -1)
seen = np.zeros(N, bool); orbs = []
for s in range(N):
    if seen[s]: continue
    cyc = []; x = s
    while not seen[x]:
        seen[x] = True; cyc.append(x); x = gp[x]
    orbs.append(cyc)
for idx, c in enumerate(orbs):
    for x in c: orbit_of[x] = idx
# vertices: orbit ids of reps
vid = {int(orbit_of[rep[i]]): i for i in range(M)}
# self-collinear orbits
selfc = set()
adj = {}
for (a, b) in pairs:
    oa, ob = orbit_of[a], orbit_of[b]
    if oa == ob: selfc.add(oa)
    else:
        adj.setdefault(oa, set()).add(ob); adj.setdefault(ob, set()).add(oa)
print('orbits total', len(orbs), 'self-collinear orbits', len(selfc), 'vertices', M, 'non-vertex orbits', len(orbs)-M)
print('vertices that are self-collinear:', sum(1 for o in vid if o in selfc))
mism = 0; tot = 0
for i in range(M):
    o = orbit_of[rep[i]]
    g_nb = set(vid[x] for x in adj.get(o, set()) if x in vid)
    ours = set(nb[i].tolist())
    tot += 1
    if g_nb != ours: mism += 1
print('vertices whose neighbour list differs from geometry:', mism, 'of', tot)
np.save('/home/user/degree-diameter/research/squads/d16D7_r2/c8/pt_orbit_of.npy', orbit_of)
