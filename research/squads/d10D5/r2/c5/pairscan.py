#!/usr/bin/env python3
"""pairscan.py GQBIN SEED M OUT.tsv: card c5 round 2.  Element = power of a random PGSp(4,7) element with all point cycles
of length M (semiregular); feasible single M-orbits (exact matching == N); then EVERY disjoint pair of feasible orbits:
writes OUT.tsv lines  size cp cl flags  (size = exact matching size of the union, cp/cl = collinear freed-point pairs /
concurrent freed-line pairs).  usage: python3 -I pairscan.py gq/gq_q7.bin 201 5 pairs5_201.tsv"""
import sys, random, time
sys.path.insert(0, '.')
from sym import *
fn, seed, m, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
Mt = Matcher(q, N, lines, lof)
flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]

def semireg_power(rng):
    for _ in range(300000):
        M = random_elem(rng)
        pp = perm_points(M, coords, index)
        o = order_of(cycle_type(pp))
        if o % m: continue
        P = list(range(N))
        for _ in range(o // m): P = [pp[x] for x in P]
        if cycle_type(P) == {m: N // m}: return P

def ucount(U):
    cp = sum(1 for i in range(len(U)) for j in range(i) if Mt.Pm[U[i][0]] >> U[j][0] & 1)
    cl = sum(1 for i in range(len(U)) for j in range(i) if Mt.Lm[U[i][1]] >> U[j][1] & 1)
    return cp, cl

t0 = time.time()
pp = semireg_power(rng)
pl = perm_lines(pp, lines, lidx)
orbs = [ob for ob in flag_orbits(pp, pl, flags_all) if len({p for p, _ in ob}) == len(ob) and len({l for _, l in ob}) == len(ob)]
feas = [ob for ob in orbs if Mt.size(ob)[0] == N]
print('orbits', len(orbs), 'feasible singles', len(feas), 'time %.1f' % (time.time() - t0), flush=True)
cnt = 0
with open(out, 'w') as f:
    for i in range(len(feas)):
        for j in range(i):
            A, B = feas[i], feas[j]
            if {p for p, _ in A} & {p for p, _ in B} or {l for _, l in A} & {l for _, l in B}: continue
            U = A + B
            sz = Mt.size(U)[0]; cp, cl = ucount(U)
            f.write(f"{sz} {cp} {cl} " + ' '.join(f'{p}:{l}' for p, l in U) + '\n'); cnt += 1
print('pairs written', cnt, 'time %.1f' % (time.time() - t0), flush=True)
