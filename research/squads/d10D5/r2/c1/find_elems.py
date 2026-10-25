#!/usr/bin/env python3
"""find_elems.py SEED TRIES M: random PGSp(4,7) elements; for each element g of order divisible by M take h = g^(o/M)
and keep h if its point AND line permutations are semiregular of order M (all cycles length M).
usage: python3 -I find_elems.py gq/gq_q7.bin SEED TRIES M  -> writes elems_M_SEED.txt (one point perm per line)."""
import sys, random, math, time
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; seed = int(sys.argv[2]); tries = int(sys.argv[3]); M = int(sys.argv[4])
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
def pcomp(a, b): return [a[b[i]] for i in range(len(b))]          # a after b
def ppow(a, e):
    r = list(range(len(a))); base = a[:]
    while e:
        if e & 1: r = pcomp(base, r)
        base = pcomp(base, base); e >>= 1
    return r
def porder(a):
    return math.lcm(*cycle_type(a).keys()) if cycle_type(a) else 1
orders = {}
found = []
seen = set()
t0 = time.time()
for t in range(tries):
    Mx = random_elem(rng)
    pp = perm_points(Mx, coords, index)
    o = porder(pp)
    orders[o] = orders.get(o, 0) + 1
    if o % M: continue
    h = ppow(pp, o // M)
    ct = cycle_type(h)
    if ct != {M: N // M}: continue
    pl = perm_lines(h, lines, lidx)
    if cycle_type(pl) != {M: N // M}: continue
    key = tuple(h)
    if key in seen: continue
    seen.add(key); found.append(h)
print('orders seen (order: count):', sorted(orders.items()), 'time %.1f' % (time.time() - t0))
print('semiregular order', M, 'elements found', len(found), flush=True)
with open(f'elems_{M}_{seed}.txt', 'w') as f:
    for h in found: f.write(' '.join(map(str, h)) + '\n')
