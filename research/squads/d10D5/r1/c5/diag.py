import sys, random, collections
sys.path.insert(0, '.')
from sym import *
q, N, lines, lof, coords = load_all('gq/gq_q7.bin')
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
assert len(index) == N and len(lidx) == len(lines)
rng = random.Random(5)
cnt = collections.Counter(); ex = {}
bad = 0
for e in range(300):
    Mx = random_elem(rng)
    if sim_lambda(Mx) is None: bad += 1; continue
    pp = perm_points(Mx, coords, index)
    assert sorted(pp) == list(range(N))
    pl = perm_lines(pp, lines, lidx)
    ct = cycle_type(pp); o = order_of(ct)
    cnt[o] += 1
    ex.setdefault(o, (tuple(sorted(ct.items())), Mx))
print('nonsim', bad, 'orders', sorted(cnt.items()))
for o in sorted(ex): print(o, ex[o][0])
