import sys, random, time
sys.path.insert(0, '.')
from sym import *
rng = random.Random(7)
q, N, lines, lof, coords = load_all('gq/gq_q7.bin')
index = {c: i for i, c in enumerate(coords)}
t0 = time.time(); hits = {}; tries = 0
while time.time() - t0 < 60:
    M = random_elem(rng); tries += 1
    pp = perm_points(M, coords, index)
    o = order_of(cycle_type(pp))
    if o % 4: continue
    P = list(range(N))
    for _ in range(o // 4): P = [pp[x] for x in P]
    ct = cycle_type(P)
    key = tuple(sorted(ct.items()))
    hits[key] = hits.get(key, 0) + 1
print('tries', tries, 'time %.0f' % (time.time() - t0))
for k, v in sorted(hits.items(), key=lambda t: -t[1])[:8]: print(k, v)
