#!/usr/bin/env python3
"""pairscan2.py GQBIN SEED M1 M2 OUT.tsv: card c5 round 2, k = 9 shape (orbit of order M1 + orbit of order M2 = 4 + 5).
Two semiregular elements (powers of random PGSp(4,7) elements, all point cycles of length M1 resp. M2); feasible single
orbits of each (exact matching == N); every disjoint CROSS pair (one orbit from each) written to OUT.tsv as
  size cp cl flags   (size = exact matching size of the union, cp / cl = collinear freed-point / concurrent freed-line pairs).
usage: python3 -I pairscan2.py gq/gq_q7.bin 301 4 5 pairs45_301.tsv"""
import sys, random, time
sys.path.insert(0, '.')
from sym import *
fn, seed, m1, m2, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
Mt = Matcher(q, N, lines, lof)
flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]


def semireg_power(rng, m):
    for _ in range(300000):
        M = random_elem(rng)
        pp = perm_points(M, coords, index)
        o = order_of(cycle_type(pp))
        if o % m: continue
        P = list(range(N))
        for _ in range(o // m): P = [pp[x] for x in P]
        if cycle_type(P) == {m: N // m}: return P


def singles(pp):
    pl = perm_lines(pp, lines, lidx)
    orbs = [ob for ob in flag_orbits(pp, pl, flags_all) if len({p for p, _ in ob}) == len(ob) and len({l for _, l in ob}) == len(ob)]
    return [ob for ob in orbs if Mt.size(ob)[0] == N]


def ucount(U):
    cp = sum(1 for i in range(len(U)) for j in range(i) if Mt.Pm[U[i][0]] >> U[j][0] & 1)
    cl = sum(1 for i in range(len(U)) for j in range(i) if Mt.Lm[U[i][1]] >> U[j][1] & 1)
    return cp, cl


t0 = time.time()
A1 = singles(semireg_power(rng, m1))
A2 = singles(semireg_power(rng, m2))
print('feasible singles: order', m1, len(A1), ' order', m2, len(A2), 'time %.1f' % (time.time() - t0), flush=True)
cap = int(sys.argv[6]) if len(sys.argv) > 6 else 4000
cross = [(A, B) for A in A1 for B in A2]
rng.shuffle(cross)
cnt = 0
with open(out, 'w') as f:
    for A, B in cross:
        if cnt >= cap: break
        if {p for p, _ in A} & {p for p, _ in B} or {l for _, l in A} & {l for _, l in B}: continue
        U = A + B
        sz = Mt.size(U)[0]; cp, cl = ucount(U)
        f.write(f"{sz} {cp} {cl} " + ' '.join(f'{p}:{l}' for p, l in U) + '\n'); cnt += 1
print('cross pairs written', cnt, 'of', len(cross), 'time %.1f' % (time.time() - t0), flush=True)
