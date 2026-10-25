"""Cross-side check for two hub families: every L-hub / P-hub pair must be within 7 through the main graph,
i.e. min over used levels i (of L) and j (of P) of d(L_slot_i, P_vertex_j) <= 5 (or a hub edge).
Usage: crosscheck.py LFAM PFAM"""
import sys, numpy as np
C8 = '/home/user/degree-diameter/research/squads/d12D7-r2/c8'
DL = np.fromfile(C8 + '/tables/dist_L.bin', dtype=np.uint8).reshape(560, 3640)
vidP = [int(x) for x in open(C8 + '/tables/vid_P.txt').read().split()]
def read_fam(fn):
    t = open(fn).read().split(); K = int(t[0]); rows = []
    for h in range(K): rows.append([int(x) for x in t[1 + 5 * h:6 + 5 * h]])
    return rows
L = read_fam(sys.argv[1]); P = read_fam(sys.argv[2])
bad = 0; worst = 0
for h in L:
    ls = [s for s in h if s >= 0]
    for k in P:
        ps = [s for s in k if s >= 0]
        d = min(int(DL[s, vidP[t]]) for s in ls for t in ps)
        worst = max(worst, d)
        if d > 5: bad += 1
print('L hubs', len(L), 'P hubs', len(P), 'cross pairs with distance > 5 (i.e. > 7 total):', bad, 'worst main distance', worst)
