import random, sys, collections, time
import numpy as np
import sp
from clique import max_union
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
orders = collections.Counter()
seen = {}
t0 = time.time()
for trial in range(400):
    M = sp.random_sp(rng, 25)
    p = sp.perm_of_matrix(M)
    d = sp.perm_order(p)
    orders[d] += 1
    seen.setdefault(d, p)
print('order distribution (point-perm order):', sorted(orders.items()))
for d in sorted(seen):
    p = seen[d]
    cyc = sp.cycles(p)
    sizes = collections.Counter(len(c) for c in cyc)
    good = [c for c in cyc if not sp.collinear_pairs_inside(c)]
    print('order', d, 'cycle sizes', sorted(sizes.items()), 'good orbits', len(good))
