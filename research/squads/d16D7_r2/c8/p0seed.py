import numpy as np, sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
q, N, L, LP, X = load_hex()
M, E, rep_p, nb_p = load_og(D+'og_pts.txt')
M2, E2, rep_l, nb_l = load_og(D+'og_lines.txt')
gp = load_perm(D+'data/g13o61_pts.bin'); gl = load_perm(D+'data/g13o61_lines.bin')
a = X[:, 3]
a0 = a == 0
c0 = a0[LP].sum(axis=1)
inside = np.where(c0 == 14)[0]
# orbits of lines
from geo import orbits_of
orbit_l, orbs_l = orbits_of(gl)
orbit_p, orbs_p = orbits_of(gp)
# inside-line orbits
io = sorted(set(orbit_l[inside]))
print('inside line orbits', len(io))
# for each inside line orbit pick a generic point (on exactly one inside line) on its representative line
cnt_in = np.bincount(LP[inside].ravel(), minlength=N)
vid_p = {}
for i in range(M): vid_p[int(orbit_p[rep_p[i]])] = i
chosen = []
for o in io:
    line = orbs_l[o][0]
    pts = [p for p in LP[line] if cnt_in[p] == 1]
    x = pts[0]
    v = int(orbit_p[x])
    chosen.append(vid_p[v])
print('chosen point-vertices', len(chosen), 'distinct', len(set(chosen)))
# check independence with og adjacency
S = set(chosen)
bad = sum(1 for i in chosen for j in nb_p[i] if int(j) in S)
print('edges inside P0 transversal', bad)
with open('seedA_pts.txt', 'w') as f:
    f.write('\n'.join(map(str, chosen)) + '\n')
# neighbourhood of seed in full graph
killed = set()
for i in chosen: killed.update(int(j) for j in nb_p[i])
cand = [i for i in range(M) if i not in S and i not in killed]
print('killed by seed', len(killed), 'candidates', len(cand))
print('candidate classes a0:', sum(1 for i in cand if a[rep_p[i]] == 0), 'affine:', sum(1 for i in cand if a[rep_p[i]] != 0))
