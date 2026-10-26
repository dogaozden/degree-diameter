import sys, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c2')
from orb import *
rng = random.Random(int(sys.argv[1]))
want = [int(x) for x in sys.argv[2].split(',')]
t0 = time.time()
seen_orders = {}
for trial in range(int(sys.argv[3])):
    g = random_symp(rng, k=rng.randrange(3, 12))
    m = order_of(g)
    if m is None or m == 1: continue
    for d in want:
        if m % d: continue
        if seen_orders.get(d, 0) >= int(sys.argv[4]): continue
        seen_orders[d] = seen_orders.get(d, 0) + 1
        h = mpow(g, m // d)
        perm = perm_of(h)
        orbs = orbits_of_perm(perm)
        good = usable_orbits(orbs)
        t1 = time.time()
        sz, S = max_union(good)
        print('d', d, 'elem', m, 'orbits', len(orbs), 'usable', len(good), 'score', sz, 'time', round(time.time() - t1, 1), flush=True)
        if sz > 0:
            json.dump({'size': sz, 'order': d, 'S': S}, open('/home/user/degree-diameter/research/squads/gqd5-r1/c2/cand_d%d_seed%s.json' % (d, sys.argv[1]), 'w'))
print('total', time.time() - t0)
