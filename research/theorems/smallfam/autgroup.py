"""Automorphism group order (igraph / BLISS), vertex orbits, girth and diameter of a metacyclic Haar graph.
Usage: python3 autgroup.py m k r a1,j1 a2,j2 ...   (S as (a,j) pairs; G = Z_m x|_r Z_k)"""
import sys

import igraph as ig


def build(m, k, r, S):
    rp = [pow(r, j, m) for j in range(k)]
    N = m * k
    edges = []
    for a in range(m):
        for j in range(k):
            g = a * k + j
            for (sa, sj) in S:
                h = ((sa + rp[sj] * a) % m) * k + (sj + j) % k     # s g
                edges.append((g, N + h))
    return ig.Graph(n=2 * N, edges=edges), N


if __name__ == '__main__':
    m, k, r = map(int, sys.argv[1:4])
    S = [tuple(map(int, x.split(','))) for x in sys.argv[4:]]
    G, N = build(m, k, r, S)
    aut = G.count_automorphisms()
    gens = G.automorphism_group()
    # does some automorphism swap the colour classes?
    swap = any(g[0] >= N for g in gens) or any(any((v < N) != (g[v] < N) for v in range(0, 2 * N, max(1, N // 50))) for g in gens)
    print(f'n={2*N} edges={G.ecount()} degree={max(G.degree())} diameter={G.diameter()} girth={G.girth()} '
          f'|Aut|={aut} |Aut|/N={aut / N:g} colour-swapping automorphism: {swap}')
