# Simulated annealing: choose 16 disjoint edges (a_i,b_i) of the flag graph so that the b_i cover A within radius 3
# and the a_i cover B within radius 3 (C[b,a] = dist(a,b) <= 3 is symmetric in the roles).
import sys, random, time, numpy as np
from cov import biadj, ball3_B
path, seed, iters = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rnd = random.Random(seed)
n, nA, M, E = biadj(path)
C = ball3_B(M)                       # C[b_idx, a] (b_idx = B-index)
adjA = [[] for _ in range(nA)]
for u, v in E: adjA[u].append(v - nA)
Ebs = E
K = 16
edges = rnd.sample(E, K)
# make a,b distinct
def ok(es):
    return len({u for u, v in es}) == K and len({v for u, v in es}) == K
while not ok(edges):
    edges = rnd.sample(E, K)
ai = [u for u, v in edges]; bi = [v - nA for u, v in edges]
cntA = C[bi].sum(axis=0).astype(np.int32)             # coverage of A by the b's
cntB = C[:, ai].sum(axis=1).astype(np.int32)          # coverage of B by the a's
cost = int((cntA == 0).sum() + (cntB == 0).sum())
best = cost; t0 = time.time(); T0, T1 = float(sys.argv[4]), float(sys.argv[5])
usedA = set(ai); usedB = set(bi)
for it in range(iters):
    T = T0 * (T1 / T0) ** (it / iters)
    i = rnd.randrange(K)
    # new edge: random B, random neighbour A, both unused
    e = E[rnd.randrange(len(E))]
    a2, b2 = e[0], e[1] - nA
    if a2 in usedA or b2 in usedB: continue
    a1, b1 = ai[i], bi[i]
    nA_ = cntA - C[b1] + C[b2]
    nB_ = cntB - C[:, a1] + C[:, a2]
    nc = int((nA_ == 0).sum() + (nB_ == 0).sum())
    d = nc - cost
    if d <= 0 or rnd.random() < np.exp(-d / T):
        cntA, cntB, cost = nA_, nB_, nc
        usedA.discard(a1); usedB.discard(b1); usedA.add(a2); usedB.add(b2)
        ai[i], bi[i] = a2, b2
        if cost < best:
            best = cost
        if cost == 0: break
    if it % 20000 == 0: print('it', it, 'T', round(T, 3), 'cost', cost, 'best', best, 'time', round(time.time() - t0), flush=True)
print('final cost', cost, 'best', best, 'iters', it, flush=True)
if cost == 0:
    out = [(ai[i], bi[i] + nA) for i in range(K)]
    with open(f'match_seed{seed}.txt', 'w') as f:
        for a, b in out: f.write(f'{a} {b}\n')
    print('FOUND matching', out)
