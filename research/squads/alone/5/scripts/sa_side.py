# S_B = N(a*) (16 B-vertices, already radius-3 dominating A). Choose a_i in N(b_i), distinct, so that the a_i
# radius-3 dominate B. Cost = uncovered B. SA over the choice of partner for each b_i.
import sys, random, numpy as np
from cov import biadj, ball3_B
path, astar, seed, iters = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rnd = random.Random(seed)
n, nA, M, E = biadj(path)
C = np.load('C3.npy')                       # C[b_index, a] = dist(a, b) <= 3
adjA = [[] for _ in range(nA)]; adjB = [[] for _ in range(nA)]
for u, v in E: adjA[u].append(v - nA); adjB[v - nA].append(u)
bs = adjA[astar]                            # B-indices of N(a*)
cand = {b: adjB[b] for b in bs}             # A-candidates for each b (its 16 A-neighbours)
choice = {b: rnd.choice(cand[b]) for b in bs}
def fix_distinct():
    used = set()
    for b in bs:
        if choice[b] in used:
            opts = [a for a in cand[b] if a not in used]
            if not opts: return False
            choice[b] = rnd.choice(opts)
        used.add(choice[b])
    return len(used) == len(bs)
while not fix_distinct(): pass
cnt = np.zeros(nA, dtype=np.int32)
for b in bs: cnt += C[:, choice[b]]
cost = int((cnt == 0).sum()); best = cost; print('init cost', cost, flush=True)
T0, T1 = float(sys.argv[5]), float(sys.argv[6])
for it in range(iters):
    T = T0 * (T1 / T0) ** (it / iters)
    b = bs[rnd.randrange(len(bs))]
    new = rnd.choice(cand[b]); old = choice[b]
    if new == old or new in {choice[x] for x in bs}: continue
    nc_arr = cnt - C[:, old] + C[:, new]
    nc = int((nc_arr == 0).sum())
    d = nc - cost
    if d <= 0 or rnd.random() < np.exp(-d / T):
        cnt = nc_arr; cost = nc; choice[b] = new
        best = min(best, cost)
        if cost == 0: break
    if it % 5000 == 0: print('it', it, 'T', round(T, 3), 'cost', cost, 'best', best, flush=True)
print('final cost', cost, 'best', best, flush=True)
if cost == 0:
    pairs = [(choice[b], b + nA) for b in bs]
    with open(f'side_{astar}_{seed}.txt', 'w') as f:
        for a, bb in pairs: f.write(f'{a} {bb}\n')
    print('FOUND', pairs)
