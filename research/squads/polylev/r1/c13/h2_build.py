"""c13 part 2: K pairwise disjoint lines + K pairwise non-collinear points in H(2), colour files for the D = 11 lift.
Usage: python3 h2_build.py K [seed] -> writes pc2_K.bin (point colours), lc2_K.bin (line colours), prints the sets.
Maximum independent sets are found by iterated local search (the counting bound is 21 = 63/3 on both sides).
"""
import sys
import random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q2.bin'
H = Hex(HEX)
N, q = H.N, H.q
assert N == 63 and q == 2
LP = [list(map(int, H.lines[l])) for l in range(N)]          # points on each line
PL = [list(map(int, H.PL[p])) for p in range(N)]              # lines through each point


def graph(sets):
    """adjacency lists: a ~ b when the two elements share an incidence (sets[a] & sets[b])"""
    adj = [[] for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if a != b and set(sets[a]) & set(sets[b]):
                adj[a].append(b)
    return adj


def ils_mis(adj, iters=300, swaps=60, seed=1):
    """iterated local search for a large independent set: bounded (1,1)-swap plateau walks, greedy fill and random
    forced insertions. Heuristic (no optimality claim); the counting bound is 21 = 63/3 on both sides."""
    rnd = random.Random(seed)
    n = len(adj)

    def fill(S):
        free = [v for v in range(n) if v not in S and not any(u in S for u in adj[v])]
        rnd.shuffle(free)
        for v in free:
            if not any(u in S for u in adj[v]):
                S.add(v)
        return S

    S = fill(set())
    best = set(S)
    for _ in range(iters):
        for _ in range(swaps):
            one = [v for v in range(n) if v not in S and sum(1 for u in adj[v] if u in S) == 1]
            if not one:
                break
            v = rnd.choice(one)
            u = next(u for u in adj[v] if u in S)
            S.discard(u)
            S.add(v)
            fill(S)
            if len(S) > len(best):
                best = set(S)
        S = set(best) if rnd.random() < 0.5 else set(S)
        v = rnd.randrange(n)
        if v not in S:                       # perturbation: force a random vertex in
            for u in adj[v]:
                S.discard(u)
            S.add(v)
            fill(S)
    return sorted(best)


ADJ_LINES = graph(LP)   # lines are the elements; adjacent when they share a point (not disjoint)
ADJ_POINTS = graph(PL)  # points are the elements; adjacent when collinear (share a line)


if __name__ == '__main__':
    K = int(sys.argv[1])
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    sl = ils_mis(ADJ_LINES, seed=seed)
    sp = ils_mis(ADJ_POINTS, seed=seed)
    print(f'partial spread (pairwise disjoint lines) found: {len(sl)}; '
          f'pairwise non-collinear points found: {len(sp)}; counting bound 21')
    assert K <= len(sl) and K <= len(sp), 'K larger than the sets found'
    lines_sel = sl[:K]
    pts_sel = sp[:K]
    assert all(not (set(LP[a]) & set(LP[b])) for a in lines_sel for b in lines_sel if a < b)
    assert all(not (set(PL[a]) & set(PL[b])) for a in pts_sel for b in pts_sel if a < b)
    cp = -np.ones(N, dtype=np.int32)
    cl = -np.ones(N, dtype=np.int32)
    for i, l in enumerate(lines_sel):
        for p in LP[l]:
            cp[p] = i
    for i, p in enumerate(pts_sel):
        for l in PL[p]:
            cl[l] = i
    cp.tofile(f'pc2_{K}.bin')
    cl.tofile(f'lc2_{K}.bin')
    print('K =', K, 'lines', lines_sel, 'points', pts_sel)
    print('point colour counts', np.bincount(cp[cp >= 0]).tolist(), 'line colour counts',
          np.bincount(cl[cl >= 0]).tolist())
