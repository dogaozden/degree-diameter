"""c12: annealing for a point set T of Q(4,q) maximising |T| - LAM * sum_x max(0, deg_T(x) - 1)
(deg_T(x) = number of T-points collinear with x, x in T).  T = ovoid start.  usage: pairsa.py q iters seed LAM out.json"""
import sys, json, random, math; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c12')
from hdlib import setup
from ovoids import ovoid_avoiding
import numpy as np
q, iters, seed, LAM, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
Wq, G, ov = setup(q)
N = G.np
col = [list(set(np.nonzero(G.col[p])[0]) - {p}) for p in range(N)]
rng = random.Random(seed)
inT = [False] * N
for p in ov: inT[p] = True
deg = [0] * N                       # T-neighbours of each point (counted for all points)
for p in ov:
    for x in col[p]: deg[x] += 1
def pen(x):  # penalty contributed by point x if it is in T
    return max(0, deg[x] - 1)
size = len(ov)
viol = sum(max(0, deg[x] - 1) for x in ov)
best = (size if viol == 0 else -1, list(ov))
T0 = 0.5
for it in range(iters):
    temp = T0 * (1 - it / iters) + 0.02
    p = rng.randrange(N)
    if inT[p]:
        # remove p
        dv = -(max(0, sum(1 for x in col[p] if inT[x]) ) > 0) * 0  # placeholder
        nb = [x for x in col[p] if inT[x]]
        # change in violations: removing p lowers deg of its T-neighbours
        dviol = 0
        for x in nb:
            dviol -= 1 if deg[x] - 1 >= 1 else 0   # x loses one T-neighbour (x in T)
        # p's own penalty goes away
        dviol -= max(0, deg[p] - 1)
        dsize = -1
        delta = dsize * 1.0 - LAM * dviol
        if delta >= 0 or rng.random() < math.exp(delta / temp):
            inT[p] = False; size -= 1; viol += dviol
            for x in col[p]: deg[x] -= 1
    else:
        nb = [x for x in col[p] if inT[x]]
        dviol = 0
        for x in nb:
            dviol += 1 if deg[x] >= 1 else 0          # x (in T) gets one more T-neighbour
        dviol += max(0, deg[p] + 0 - 0)               # p's own penalty as a member: max(0, deg[p]-1)
        dviol = dviol + (max(0, deg[p] - 1) if False else 0)
        pen_new = max(0, deg[p] - 1)
        dviol = sum(1 for x in nb if deg[x] >= 1) + pen_new
        delta = 1.0 - LAM * dviol
        if delta >= 0 or rng.random() < math.exp(delta / temp):
            inT[p] = True; size += 1; viol += dviol
            for x in col[p]: deg[x] += 1
    if viol == 0 and size > best[0]:
        best = (size, [x for x in range(N) if inT[x]])
# recompute exactly
T = best[1]
ok = all(sum(1 for y in T if y in set(col[x])) <= 1 for x in T)
json.dump(sorted(T), open(out, 'w'))
print('q', q, 'best pair-rule size', len(T), 'verified', ok)
