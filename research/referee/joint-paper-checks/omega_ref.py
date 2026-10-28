"""Referee check of Definition 7.1 / Corollary 7.4: Gomez's Omega_q with the thesis labelling (one random pair of
bijections P_0, L_0 for all copies), readings 1 and 2, for q=2,3; the diameter is computed by apsp64."""
import sys, random
from hexagon import Hex, write_edges
def build(q, pattern, reading, seed=0):
    random.seed(seed)
    H = Hex(q); N = H.N; alpha = (q + 3) // 2; assert len(pattern) == alpha
    P0 = list(range(N)); random.shuffle(P0); L0 = list(range(N)); random.shuffle(L0)
    ncop = 5 * alpha; V = lambda c, e: 2 * N * c + e   # e < N point, e >= N line N+k
    edges = []
    for c in range(ncop):
        for k in range(N):
            for i in H.lines[k]: edges.append((V(c, i), V(c, N + k)))
    hub0 = 2 * N * ncop
    hub = lambda t, k, bar: hub0 + (10 * t + 5 * bar + k)
    for c in range(ncop):
        B, i = divmod(c, 5); tp = pattern[B]
        inner = ('L' if reading == 1 else ('P' if tp == 'a' else 'L'))
        outer = 'P' if inner == 'L' else 'L'
        if tp == 'a': unb, bar = {(i - 1) % 5, (i + 1) % 5}, {(i + 2) % 5, (i + 3) % 5}; su, sb = inner, outer
        else: unb, bar = {(i + 1) % 5, (i + 2) % 5}, {(i - 1) % 5, (i + 1) % 5}; su, sb = outer, inner
        for t in range(N):
            for k in unb: edges.append((hub(t, k, 0), V(c, P0[t] if su == 'P' else N + L0[t])))
            for k in bar: edges.append((hub(t, k, 1), V(c, P0[t] if sb == 'P' else N + L0[t])))
    n = hub0 + 10 * N
    return n, edges
if __name__ == '__main__':
    for arg in sys.argv[1:]:
        q, pat, rd = arg.split(',')
        n, e = build(int(q), pat, int(rd))
        fn = f"omega_q{q}_{pat}_r{rd}.edges"; write_edges(fn, n, e); print(fn, n)
