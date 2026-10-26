"""Plateau search for partial ovoids of W(9): (1,1)-swaps and free-point additions with tabu, from a seed set."""
import sys, json, random, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
G = gqlib.W(9)
COL = G.col
NP = G.np
nbrs = [np.nonzero(COL[p])[0].tolist() for p in range(NP)]
seed_file, out_file, iters, rs = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
rnd = random.Random(rs)
S0 = json.load(open(seed_file))
inS = np.zeros(NP, bool)
cnt = np.zeros(NP, np.int64)   # number of S-points collinear with p
def add(p):
    inS[p] = True
    for u in nbrs[p]: cnt[u] += 1
def rem(p):
    inS[p] = False
    for u in nbrs[p]: cnt[u] -= 1
for p in S0: add(p)
best = [int(x) for x in np.nonzero(inS)[0]]
tabu = np.zeros(NP, np.int64)
t0 = time.time()
for it in range(iters):
    free = np.nonzero((~inS) & (cnt == 0))[0]
    if len(free):
        p = int(free[rnd.randrange(len(free))]); add(p)
        if inS.sum() > len(best):
            best = [int(x) for x in np.nonzero(inS)[0]]
            json.dump(sorted(best), open(out_file, 'w'))
            print('it', it, 'size', len(best), 'time %.0f' % (time.time() - t0), flush=True)
        continue
    # one-swap: p with cnt==1 whose only conflict is a point s in S
    cand = np.nonzero((~inS) & (cnt == 1) & (tabu <= it))[0]
    if len(cand) == 0:
        continue
    p = int(cand[rnd.randrange(len(cand))])
    s = [u for u in nbrs[p] if inS[u]][0]
    rem(s); add(p)
    tabu[s] = it + 7 + rnd.randrange(10)
print('final best', len(best), flush=True)
