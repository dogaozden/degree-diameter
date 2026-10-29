#!/usr/bin/env python3
"""Scorer for a non-friendly (H -> H) transition of the diameter-7 level graphs (D7_HEXAGON.md Definition 3.2).
Two copies of H(q): level 0 and level 1, each the incidence graph; matching edges (p, 0) ~ (sigma(p), 1) for every point
p NOT in R (sigma: points -> lines, a bijection). The transition is "repaired" iff every vertex of level 0 is within
distance 7 of every vertex of level 1 in this graph. Prints the number of ordered (level-0, level-1) pairs at distance
> 7 (0 = repaired) and |R|. Exact (bitset BFS from every level-0 vertex).
usage: transcheck.py HEXBIN SIGMA R      SIGMA: file of N line indices (sigma[p] for p = 0..N-1), or a lab "multi"
                                          .sol (sigma on lines 4.., R = its "freed" line if R is '-')
       R: file of point indices (whitespace separated) or '-'"""
import sys
import numpy as np
from hexload import load


def bad_pairs(q, N, LP, PL, sig, R, chunk=2048):
    free = np.zeros(N, bool); free[R] = True
    # vertex ids: level0 point p -> p, level0 line l -> N + l, level1 point -> 2N + p, level1 line -> 3N + l
    nb = [[] for _ in range(4 * N)]
    adjP = np.concatenate([PL + N, PL + 3 * N]); adjL = np.concatenate([LP, LP + 2 * N])
    # padded neighbour table (degree <= q + 2)
    D = q + 2; T = np.full((4 * N, D), -1, np.int64)
    T[:N, :q + 1] = PL + N; T[N:2 * N, :q + 1] = LP; T[2 * N:3 * N, :q + 1] = PL + 3 * N; T[3 * N:, :q + 1] = LP + 2 * N
    keep = np.nonzero(~free)[0]
    T[keep, q + 1] = 3 * N + sig[keep]
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    lk = 3 * N + np.arange(N); src = sinv; ok = ~free[src]
    T[lk[ok], q + 1] = src[ok]
    T[T < 0] = 4 * N                                   # dummy vertex with empty set
    total = 0
    srcs = np.arange(2 * N)
    for c0 in range(0, 2 * N, chunk):
        S = srcs[c0:c0 + chunk]; k = len(S); W = (k + 63) // 64
        vis = np.zeros((4 * N + 1, W), np.uint64)
        vis[S, np.arange(k) // 64] |= np.left_shift(np.uint64(1), (np.arange(k) % 64).astype(np.uint64))
        for _ in range(7):
            nv = vis.copy()
            for t in range(D):
                nv[:4 * N] |= vis[T[:, t]]
            nv[4 * N] = 0
            vis = nv
        full = np.full(W, ~np.uint64(0), np.uint64)
        if k % 64:
            full[-1] = np.uint64((1 << (k % 64)) - 1)
        miss = vis[2 * N:4 * N] ^ full
        total += int(sum(bin(int(x)).count('1') for x in miss[miss != 0]))
    return total


if __name__ == '__main__':
    hexfn, sigfn, rfn = sys.argv[1:4]
    q, N, LP, PL, X = load(hexfn)
    lines = open(sigfn).read().split('\n')
    if lines[0].startswith('multi'):
        sig = np.array([int(t) for s in lines[3:] for t in s.split()], dtype=np.int64)
        R = np.array([int(t) for t in lines[1].split()[1:]], dtype=np.int64) if rfn == '-' else None
    else:
        sig = np.array([int(t) for t in open(sigfn).read().split()], dtype=np.int64)
        R = None
    if R is None:
        R = np.array([int(t) for t in open(rfn).read().split()], dtype=np.int64)
    assert len(sig) == N and len(np.unique(sig)) == N, 'sigma is not a bijection'
    R = np.unique(R)
    print(f'q={q} |R|={len(R)} bad_pairs={bad_pairs(q, N, LP, PL, sig, R)}')
