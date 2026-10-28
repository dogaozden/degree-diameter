import sys, json, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c3')
from common import *
nl, nc, w, LN, pts = load_instance()
seed = json.load(open('/home/user/degree-diameter/research/theorems/d5gq/graphs/W9_relaxed_set_66.json'))
# build the state: components = pairs (collinear, line not in S) and singles covering the seed set
G = W(9)
Ts = set(seed)
# map point -> component id: singles id = p ; pairs found by lines
comp_of_single = {p: p for p in range(820)}
# find pairs in seed
pairs = []
used = set()
for p in seed:
    for r in seed:
        if p < r and G.col[p, r] and (p, r) not in used:
            # is it a pair in the seed? both have exactly one T-neighbour
            pairs.append((p, r))
pair_pts = set(x for pr in pairs for x in pr)
# count T-neighbours
nbc = {p: sum(1 for r in seed if r != p and G.col[p, r]) for p in seed}
pairs = [pr for pr in pairs if nbc[pr[0]] == 1 and nbc[pr[1]] == 1]
print("seed pairs", len(pairs), "singles", len(seed) - 2 * len(pairs))
# component ids: index of pair in instance: find by points
idx = {tuple(pts[c]): c for c in range(nc)}
state = []
for p, r in pairs:
    state.append(idx[tuple(sorted((p, r)))])
for p in seed:
    if nbc[p] == 0:
        state.append(idx[(p,)])
own = -np.ones(nl, dtype=np.int64)
for c in state:
    for l in LN[c][LN[c] >= 0]:
        assert own[l] == -1
        own[l] = c
print("state W", w[state].sum(), "lines used", (own >= 0).sum())
print("verify seed", verify(points_of(state, pts)))
free = own < 0
cand = np.all(np.where(LN >= 0, free[np.maximum(LN, 0)], True), axis=1)
print("free lines", free.sum(), "candidate comps with all lines free", cand.sum(), "singles", (cand & (w == 1)).sum())
