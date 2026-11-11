"""T-G1: friendly transitions with freed sets satisfying only (G1), no hubs.

(G1) for a set F of points: for every p in F, the points of F collinear with p all lie on one line through p.
Dual (G1) for a set of lines: for every line l of the set, the lines of the set meeting l all pass through one point of l.

Two-level checks: level 0 of type H, level 1 of type D, one transition 0 -> 1 with the identity on points, the points of
F freed (dual: level 0 type D, level 1 type H, identity on lines, lines freed). The theorem says this graph (two copies of
I joined by the partial identity matching) has diameter <= 7.
Five-level checks: types H D H D H, r = 2; the six friendly transitions get (G1) sets (points for H -> D, lines for
D -> H), the four others random bijections, nothing freed there. Main graph only (no hubs).
Negative controls: a maximal (G1) set plus one more point (so (G1) fails), two-level graph: count far pairs.

Usage: python3 t_g1.py Q [SEED]
"""
import os, sys, time
import numpy as np
import hexq
from hexq import Hex, write_edges, HERE
from levels import (Cover, identity_map, random_map, run_apsp, run_far, g1_ok, g1_greedy, r1_greedy,
                    opposite_greedy, aclass)

q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = np.random.default_rng(seed)
H = Hex(q); N = H.N
GD = os.path.join(HERE, 'graphs'); os.makedirs(GD, exist_ok=True)
pts, lns = np.arange(N), np.arange(N, 2 * N)
c, e, spread = hexq.hermitian_spread(H)
print(f'q={q} N={N} seed={seed}; Hermitian spread in x0 = {c} x4 + {e} x3: {len(spread)} lines')

def sets_points():
    S = {}
    S['spread points'] = np.unique(H.lines[spread - N].ravel())
    for s in range(2):
        S[f'greedy G1 #{s}'] = g1_greedy(H, pts, rng)
    S['greedy G1 from half spread'] = g1_greedy(H, pts, rng, start=np.unique(H.lines[spread[: len(spread) // 2] - N].ravel()))
    S['R1 pairs only'] = r1_greedy(H, pts, rng, pairs_only=True)
    S['R1 at most one partner'] = r1_greedy(H, pts, rng)
    return S

def sets_lines():
    S = {}
    ov = opposite_greedy(H, pts, rng)
    S[f'pencils of a partial ovoid ({len(ov)} pts)'] = np.unique(H.point_lines[ov].ravel())
    for s in range(2):
        S[f'greedy dual G1 #{s}'] = g1_greedy(H, lns, rng)
    S['R1 pairs only (lines)'] = r1_greedy(H, lns, rng, pairs_only=True)
    return S

def collinear_pairs(F):
    F = np.array(F); D = H.dist[np.ix_(F, F)]
    return int((D == 2).sum() // 2)

results = []
def two_level(name, F, t0, t1):
    t = time.time()
    M = identity_map(H, t0, t1)
    C = Cover(H, [t0, t1], [(0, 1, M, F)])
    path = os.path.join(GD, f'g1_q{q}_two.edges')
    write_edges(path, C.n_main(), C.main_edges())
    out = run_apsp(path, q + 2, 7)
    line = out.splitlines()[-1]
    print(f'  two-level {t0}->{t1} {name}: |F|={len(F)} G1={g1_ok(H, F)} collinear pairs={collinear_pairs(F)}: '
          f'{out.splitlines()[0]} | {line} ({time.time() - t:.1f}s)')
    results.append((name, len(F), line))
    return line

print('-- point sets, H -> D')
SP = sets_points()
for name, F in SP.items():
    two_level(name, F, 'H', 'D')
print('-- line sets, D -> H')
SL = sets_lines()
for name, F in SL.items():
    two_level(name, F, 'D', 'H')

print('-- negative controls (G1 violated by one extra point), two-level H -> D')
for name in ['spread points', 'greedy G1 #0']:
    F = SP[name]
    inF = np.zeros(N, dtype=bool); inF[F] = True
    for p in rng.permutation(N):
        if not inF[p] and not g1_ok(H, np.append(F, p)):
            break
    F2 = np.append(F, p)
    C = Cover(H, ['H', 'D'], [(0, 1, identity_map(H, 'H', 'D'), F2)])
    path = os.path.join(GD, f'g1_q{q}_neg.edges')
    write_edges(path, C.n_main(), C.main_edges())
    nfar, out = run_far(path, 7)
    print(f'  {name} + point {p}: |F|={len(F2)} G1={g1_ok(H, F2)}: far ordered pairs (d > 7) = {nfar}')
    results.append((name + ' + 1 point (G1 violated)', len(F2), f'far pairs {nfar}'))

print('-- five levels H D H D H, r = 2, all six friendly transitions freed, main graph (no hubs)')
types = ['H', 'D', 'H', 'D', 'H']
plist, llist = list(SP.items()), list(SL.items())
for variant in range(2):
    tr, desc = [], []
    for j in range(5):
        for k in (1, 2):
            j2 = (j + k) % 5
            if types[j] != types[j2]:
                M = identity_map(H, types[j], types[j2])
                if types[j] == 'H':
                    nm, F = plist[(j + k + variant) % len(plist)]
                else:
                    nm, F = llist[(j + k + variant) % len(llist)]
                tr.append((j, j2, M, F)); desc.append(f'{j}->{j2}: {nm} ({len(F)})')
            else:
                tr.append((j, j2, random_map(H, types[j], types[j2], rng), []))
    C = Cover(H, types, tr)
    path = os.path.join(GD, f'g1_q{q}_five.edges')
    t = time.time()
    write_edges(path, C.n_main(), C.main_edges())
    out = run_apsp(path, q + 3, 7)
    print('  ' + '; '.join(desc))
    print(f'  variant {variant}: {out.splitlines()[0]} | {out.splitlines()[-1]} ({time.time() - t:.1f}s)')
    results.append((f'HDHDH variant {variant}', C.n_main(), out.splitlines()[-1]))
