# Z8 lift of W(q) with flag voltages 4*nu(p,l), a point->line matching sigma with doubled voltages (1,5) and plain voltage 2.
import random, sys
from gq import build
def make(G, sigma, nu, out, M=8):
    """sigma: list length N, point p -> line vertex N+L. nu: dict (p, lv) -> 0/1 for flags."""
    N = G['N']
    E = []
    for p in range(N):
        for lv in G['pl_v'][p]:
            c = 4 * nu[(p, lv)]
            for i in range(M):
                E.append((p * M + i, lv * M + (i + c) % M))
    for p in range(N):
        s = sigma[p]
        for i in range(M):
            for c in (1, 5, 2):
                E.append((p * M + i, s * M + (i + c) % M))
    with open(out, 'w') as f:
        f.write(f"{2 * N * M}\n")
        f.write('\n'.join(f"{a} {b}" for a, b in E) + '\n')
    return len(E)
def setup(q):
    G = build(q); N = G['N']
    G['pl_v'] = [[N + L for L in G['pl'][p]] for p in range(N)]
    return G
