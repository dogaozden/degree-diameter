"""Idea B v2: subgroups H of Gamma = 2^3:L3(2) (monomial phi-stabiliser, order 1344) acting on Q(6,q).
usage: python3 octo2.py q minorder npairs"""
import sys, random, time, numpy as np
sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c2')
sys.path.insert(0,'/home/user/degree-diameter/research/projects/hexagon-family/tools')
from common import *
from mwc import max_weight_clique
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
q = int(sys.argv[1]); minord = int(sys.argv[2]); npairs = int(sys.argv[3])
OUT = '/home/user/degree-diameter/research/squads/hexfam_r1/c2/'
t0 = time.time()
mons = monomial_phi_group()
G, conj = setup(q, mons)
idx = {M.tobytes(): i for i, M in enumerate(mons)}
permcache = {}
def perm_of(i):
    if i not in permcache: permcache[i] = G.perm(conj(mons[i]))
    return permcache[i]
def orbit_lab(perms):
    N = G.N
    rows = np.concatenate([np.arange(N) for _ in perms]); cols = np.concatenate(perms)
    A = coo_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(N, N))
    _, lab = connected_components(A, directed=True, connection='weak')
    return lab
def closure_idx(gi):
    return frozenset(idx[M.tobytes()] for M in closure([mons[i] for i in gi]))
rng = random.Random(7)
subs = {}
for i in range(len(mons)):
    subs.setdefault(closure_idx([i]), [i])
for _ in range(npairs):
    a, b = rng.randrange(len(mons)), rng.randrange(len(mons))
    S = closure_idx([a, b])
    if S not in subs: subs[S] = [a, b]
print('distinct subgroups', len(subs), flush=True)
cand = {}
nsub = 0
for S, gi in subs.items():
    if len(S) < minord or len(S) == 1: continue
    perms = [perm_of(i) for i in gi]
    lab = orbit_lab(perms)
    cnt = np.bincount(lab)
    order = np.argsort(lab, kind='stable'); starts = np.concatenate([[0], np.cumsum(cnt)])
    for o in np.nonzero((cnt <= 1332) & (cnt >= 2))[0]:
        pts = order[starts[o]:starts[o+1]]
        Bm = G.B(G.C[pts], G.C[pts]) != 0
        np.fill_diagonal(Bm, True)
        if Bm.all():
            k = np.sort(pts).tobytes()
            if k not in cand: cand[k] = np.sort(pts)
    nsub += 1
groups = list(cand.values())
print('subgroups processed', nsub, 'candidate orbits', len(groups), 'total pts', sum(len(g) for g in groups), 'time', round(time.time()-t0,1), flush=True)
np.save(OUT + 'octo2_q%d_m%d_groups.npy' % (q, minord), np.array(groups, dtype=object), allow_pickle=True)
