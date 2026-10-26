import sys, json, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c3')
from common import *
nl, nc, w, LN, pts = load_instance()
seed = json.load(open('/home/user/degree-diameter/research/theorems/d5gq/graphs/W9_relaxed_set_66.json'))
G = W(9)
nbc = {p: sum(1 for r in seed if r != p and G.col[p, r]) for p in seed}
idx = {tuple(pts[c]): c for c in range(nc)}
state = []
for p in seed:
    if nbc[p] == 1:
        for r in seed:
            if r > p and G.col[p, r] and nbc[r] == 1:
                state.append(idx[(p, r)]); break
    elif nbc[p] == 0:
        state.append(idx[(p,)])
state = sorted(set(state))
print(len(state), w[state].sum())
random.seed(1)
for k in [3, 6, 10, 15, 20]:
    tot = []
    for trial in range(5):
        rem = random.sample(state, k)
        own = -np.ones(nl, dtype=np.int64)
        for c in state:
            if c in rem: continue
            for l in LN[c][LN[c] >= 0]: own[l] = c
        free = own < 0
        cand = np.all(np.where(LN >= 0, free[np.maximum(LN, 0)], True), axis=1)
        tot.append(int(cand.sum()))
    print("remove", k, "candidates", tot)
