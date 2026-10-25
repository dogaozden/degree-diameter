"""T-hub: full graphs with hubs.  B-hubs take one free A-slot in every level, A-hubs one free B-slot in every level
(slots assigned at random); the hub graph is a union of q - r random matchings, re-drawn (and K lowered if needed) until
BFS from every hub finds nothing beyond 7.  Then apsp_mt on the whole graph with d = q + 1 + r.

Usage: python3 t_hub.py Q [SEED]
"""
import os, sys, time
import numpy as np
import hexq
from hexq import Hex, write_edges, HERE
from levels import (Cover, identity_map, random_map, run_apsp, run_far, g1_greedy, opposite_greedy,
                    local_duality_map, check_H123, mirrored_greedy)

q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = np.random.default_rng(seed)
H = Hex(q); N = H.N
GD = os.path.join(HERE, 'graphs'); os.makedirs(GD, exist_ok=True)
c, e, spread = hexq.hermitian_spread(H)
pts, lns = np.arange(N), np.arange(N, 2 * N)
print(f'q={q} N={N} seed={seed}')

def inverse(M):
    Mi = -np.ones_like(M); A = np.where(M >= 0)[0]; Mi[M[A]] = A; return Mi

Rm, fRm, _ = mirrored_greedy(H, rng, 10 ** 6, N, spread)
M = local_duality_map(H, Rm, fRm, rng); Mi = inverse(M)
print(f'mirrored set |R|={len(Rm)}, distance-4 pairs {int((H.dist[np.ix_(Rm, Rm)] == 4).sum() // 2)}, '
      f'(H1,H2,H3)={check_H123(H, M, Rm)}')
spts = np.unique(H.lines[spread - N].ravel())
G1p = g1_greedy(H, pts, rng)
G1l = g1_greedy(H, lns, rng)

def cover(types, r):
    tr = []
    for j in range(len(types)):
        for k in range(1, r + 1):
            j2 = (j + k) % len(types)
            a, b = types[j], types[j2]
            if a == b == 'H': tr.append((j, j2, M, Rm))
            elif a == b == 'D': tr.append((j, j2, Mi, fRm))
            elif a == 'H': tr.append((j, j2, identity_map(H, a, b), spts if (j + k) % 2 else G1p))
            else: tr.append((j, j2, identity_map(H, a, b), G1l))
    return Cover(H, types, tr)

def hub_test(tag, types, r):
    C = cover(types, r)
    sa, sb = C.slots()
    KB, KA = min(map(len, sa)), min(map(len, sb))
    K = min(KA, KB)
    hubdeg = q - r
    path = os.path.join(GD, f'hub_q{q}_{tag}.edges')
    t = time.time()
    tries = 0
    while True:
        tries += 1
        n, E, HE = C.with_hubs(K, K, hubdeg, rng)
        write_edges(path, n, E)
        src = os.path.join(GD, f'hub_q{q}_{tag}.src')
        with open(src, 'w') as f:
            f.write(''.join(f'{v}\n' for v in range(C.n_main(), n)))
        nfar, _ = run_far(path, 7, src)
        if nfar == 0:
            break
        if tries % 10 == 0:
            K = int(K * 0.8)
    out = run_apsp(path, q + 1 + r, 7)
    print(f'  {tag} types {types} r={r}: free A-slots per level {list(map(len, sa))}, B-slots {list(map(len, sb))}; '
          f'K = {K} hubs per side (hub graph degree <= {hubdeg}, {tries} draws)')
    print(f'    {out.splitlines()[0]} | {out.splitlines()[-1]} ({time.time() - t:.1f}s)')

hub_test('HHH', 'HHH', 1)
hub_test('HDH', 'HDH', 1)
hub_test('HDHDH', 'HDHDH', 2)
