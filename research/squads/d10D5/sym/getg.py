#!/usr/bin/env python3
"""getg.py: recover the semiregular order-8 element g of PGSp(4,7) behind round 1 card c5's 8-flag orbit
(single.py seed 11, m = 8: the first element tried) and write its point and line permutations (g.txt: two lines)."""
import sys, random, os
C5 = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'r1', 'c5'); sys.path.insert(0, C5)
from sym import *
fn = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'r4', 'gq', 'gq_q7.bin')
rng = random.Random(11)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}; lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]
want = [(266, 64), (41, 289), (225, 350), (65, 202), (263, 330), (283, 130), (398, 292), (253, 247)]
for e in range(200000):
    Mx = random_elem(rng); pp = perm_points(Mx, coords, index); ct = cycle_type(pp)
    if order_of(ct) != 8 or ct != {8: N // 8}: continue
    pl = perm_lines(pp, lines, lidx)
    orb = [(266, 64)]
    while len(orb) < 8: p, l = orb[-1]; orb.append((pp[p], pl[l]))
    print('orbit of 266:64 under g:', orb, 'matches the 8 flags:', set(orb) == set(want), flush=True)
    if set(orb) == set(want):
        open('g.txt', 'w').write(' '.join(map(str, pp)) + '\n' + ' '.join(map(str, pl)) + '\n'); print('wrote g.txt')
    break
