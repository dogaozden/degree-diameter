"""T-A: plain level covers (random bijections).  T-H: one-transition surgery with a non-friendly matching M satisfying
(H1) R non-collinear, (H2) M(R) non-concurrent, (H3) M(Gamma_2(r)) = Gamma_2(M(r)) for r in R; first R pairwise
opposite (partial ovoid, cell-13-7 construction), then mirrored sets (pairs of R at distance 4). Main graphs only.

Usage: python3 t_ah.py Q [SEED]
"""
import os, sys, time
import numpy as np
import hexq
from hexq import Hex, write_edges, HERE
from levels import (Cover, identity_map, random_map, run_apsp, run_far, g1_greedy, opposite_greedy,
                    local_duality_map, check_H123, mirrored_greedy, gamma2, aclass)

q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = np.random.default_rng(seed)
H = Hex(q); N = H.N
GD = os.path.join(HERE, 'graphs'); os.makedirs(GD, exist_ok=True)
c, e, spread = hexq.hermitian_spread(H)
pts, lns = np.arange(N), np.arange(N, 2 * N)
print(f'q={q} N={N} seed={seed}')

def run(tag, C, d):
    path = os.path.join(GD, f'ah_q{q}_{tag}.edges')
    t = time.time()
    write_edges(path, C.n_main(), C.main_edges())
    out = run_apsp(path, d, 7)
    print(f'  {tag}: {out.splitlines()[0]} | {out.splitlines()[-1]} ({time.time() - t:.1f}s)')
    return path

print('-- T-A: plain level covers, random bijections')
for types, r in [('HHH', 1), ('HDH', 1), ('HHHHH', 2), ('HDHDH', 2)] + ([('HHDHHDD', 3), ('HHHHHHH', 3)] if q <= 4 else []):
    tr = [(j, j2, random_map(H, types[j], types[j2], rng), []) for j, j2 in
          [(j, (j + k) % len(types)) for j in range(len(types)) for k in range(1, r + 1)]]
    run(f'plain_{types}', Cover(H, types, tr), q + 1 + r)

def inverse(M):
    Mi = -np.ones_like(M)
    A = np.where(M >= 0)[0]
    Mi[M[A]] = A
    return Mi

def surgery_tests(tag, R, fR):
    M = local_duality_map(H, R, fR, rng)
    Mi = inverse(M)
    h = check_H123(H, M, R)
    hD = check_H123(H, Mi, fR)
    nd4 = int((H.dist[np.ix_(R, R)] == 4).sum() // 2)
    print(f'  {tag}: |R|={len(R)}, pairs of R at distance 4: {nd4}; (H1,H2,H3) for M on R: {h}; for M^-1 on M(R): {hD}')
    # three levels H H H, r = 1, the same M and R on all three transitions
    tr = [(j, (j + 1) % 3, M, R) for j in range(3)]
    run(f'{tag}_HHH', Cover(H, 'HHH', tr), q + 2)
    # H D H D H, r = 2: non-friendly H->H with (M, R), D->D with (M^-1, M(R)); friendly ones with (G1) sets
    types = 'HDHDH'
    tr = []
    for j in range(5):
        for k in (1, 2):
            j2 = (j + k) % 5
            if types[j] == types[j2] == 'H':
                tr.append((j, j2, M, R))
            elif types[j] == types[j2] == 'D':
                tr.append((j, j2, Mi, fR))
            elif types[j] == 'H':
                tr.append((j, j2, identity_map(H, 'H', 'D'), np.unique(H.lines[spread - N].ravel())))
            else:
                tr.append((j, j2, identity_map(H, 'D', 'H'), g1_greedy(H, lns, rng)))
    run(f'{tag}_HDHDH', Cover(H, types, tr), q + 3)
    return M

print('-- T-H: pairwise opposite R (partial ovoid), M(R) = spread lines, M a local duality on R')
best = None
for s in range(60 if q == 3 else 10):
    R = opposite_greedy(H, pts, rng)
    if best is None or len(R) > len(best):
        best = R
R = np.array(sorted(best))
fR = rng.permutation(spread)[:len(R)]
M = surgery_tests('opp', R, fR)

print('-- negative control: (H3) broken at one r (two values of M swapped), two levels H -> H')
r0 = int(R[0])
U = set(int(x) for x in R)
for x in R:
    U |= set(int(z) for z in gamma2(H, int(x)))
z = int(gamma2(H, r0)[0])
outside = [int(p) for p in rng.permutation(N) if int(p) not in U]
w = outside[0] if outside else int(gamma2(H, int(R[1]))[0])   # an ovoid: U is everything, swap with Gamma_2(r1)
M2 = M.copy(); M2[z], M2[w] = M[w], M[z]
for name, MM in [('intact', M), ('broken', M2)]:
    C = Cover(H, 'HH', [(0, 1, MM, R)])
    path = os.path.join(GD, f'ah_q{q}_neg.edges')
    write_edges(path, C.n_main(), C.main_edges())
    nfar, _ = run_far(path, 7)
    print(f'  two-level H->H, {name} M: (H1,H2,H3)={check_H123(H, MM, R)}: far ordered pairs (d > 7) = {nfar}')

print('-- T-H mirrored: R = R0 (pairwise opposite) + extra points at distance 4 from R0, distance-4 pattern mirrored')
for n0 in ([len(R)] if q > 3 else [len(R), len(R) // 2]):
    Rm, fRm, added = mirrored_greedy(H, rng, n0, N, spread)
    surgery_tests(f'mirror_n0_{n0}', Rm, fRm)
