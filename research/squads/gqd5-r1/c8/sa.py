"""Simulated annealing over hub structure on the 3-level test bed (H,H,D; freed R on 1->2 only).
Hubs: nB B-hubs (colour 1, may take slots at freed L1 points), nA A-hubs (colour 0, may take slots at freed L2 points),
Y: bipartite graph B-hubs x A-hubs.  Degree of every hub <= q+2.  Objective: #ordered-unordered pairs at distance > 5
(+ big penalty for degree violation).  Freed points keep degree q+1 if unassigned."""
import sys, random, time
sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from base import *
import subprocess

def build_adj(n0, A0, R, nB, nA, slotB, slotA, Y):
    n = n0 + nB + nA
    A = np.zeros((n, n), dtype=np.float32)
    A[:n0, :n0] = A0
    for y, h in slotB.items():           # freed L1 point y -> B-hub h
        if h is not None:
            A[n0 + h, y] = A[y, n0 + h] = 1
    for w, g in slotA.items():           # freed L2 point w -> A-hub g
        if g is not None:
            A[n0 + nB + g, w] = A[w, n0 + nB + g] = 1
    for h in range(nB):
        for g in range(nA):
            if Y[h][g]:
                A[n0 + h, n0 + nB + g] = A[n0 + nB + g, n0 + h] = 1
    return A

def cost(A, q, n0, nB, nA):
    n = A.shape[0]
    deg = A.sum(1)
    viol = int(np.maximum(deg[n0:] - (q + 2), 0).sum() + np.maximum(deg[:n0] - (q + 2), 0).sum())
    reach = np.eye(n, dtype=bool); fr = reach.copy(); d = 0
    while True:
        nx = ((fr.astype(np.float32) @ A) > 0) & ~reach
        if not nx.any(): break
        d += 1
        if d > 5: break
        reach |= nx; fr = nx
    bad = int((~reach).sum()) // 2
    return bad + 20 * viol, bad, viol

def run(q, R, seed, iters, nB, nA, M01, T0=2.0):
    G = getG(q)
    rng = random.Random(seed)
    n0, E, per = base_edges(G, M01, R)
    A0 = np.zeros((n0, n0), dtype=np.float32)
    for a, b in E: A0[a, b] = A0[b, a] = 1
    slotB = {y: None for y in R}; slotA = {w: None for w in R}
    Y = [[0] * nA for _ in range(nB)]
    for y in R:
        slotB[y] = rng.randrange(nB) if rng.random() < 0.7 else None
        slotA[y] = rng.randrange(nA) if rng.random() < 0.7 else None
    A = build_adj(n0, A0, R, nB, nA, slotB, slotA, Y)
    c, bad, viol = cost(A, q, n0, nB, nA)
    best = (c, bad, viol, dict(slotB), dict(slotA), [r[:] for r in Y])
    t0 = time.time()
    for it in range(iters):
        T = T0 * (1 - it / iters) + 0.05
        move = rng.random()
        oldB, oldA, oldY = dict(slotB), dict(slotA), [r[:] for r in Y]
        if move < 0.35:
            y = rng.choice(R); slotB[y] = rng.choice([None] + list(range(nB)))
        elif move < 0.7:
            w = rng.choice(R); slotA[w] = rng.choice([None] + list(range(nA)))
        else:
            h = rng.randrange(nB); g = rng.randrange(nA); Y[h][g] ^= 1
        A = build_adj(n0, A0, R, nB, nA, slotB, slotA, Y)
        c2, bad2, viol2 = cost(A, q, n0, nB, nA)
        if c2 <= c or rng.random() < np.exp(-(c2 - c) / T):
            c, bad, viol = c2, bad2, viol2
            if c < best[0]:
                best = (c, bad, viol, dict(slotB), dict(slotA), [r[:] for r in Y])
                if c == 0: break
        else:
            slotB, slotA, Y = oldB, oldA, oldY
    return best, n0, time.time() - t0

if __name__ == '__main__':
    q = int(sys.argv[1]); iters = int(sys.argv[2]); nB = int(sys.argv[3]); nA = int(sys.argv[4]); seed = int(sys.argv[5])
    G = getG(q); M = random_M01(G, 1)
    x = 0; s = G.plines[0][0]; y = [p2 for p2 in G.lines[s] if p2 != x][0]
    R = [x, y]
    best, n0, dt = run(q, R, seed, iters, nB, nA, M)
    print('R', R, 'nB', nB, 'nA', nA, 'best cost', best[0], 'bad pairs', best[1], 'degree viol', best[2], 'time', round(dt, 1))
    if best[0] == 0:
        print('VALID FOUND', best[3], best[4], best[5])
