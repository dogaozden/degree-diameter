import sys, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from quot import *
rng = random.Random(int(sys.argv[1]))
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
t0 = time.time(); seen = {}
for it in range(int(sys.argv[2])):
    g = rand_elem(E, rng, m=rng.randrange(20, 40))
    perm = perm_of(g)
    m = order_of(perm)
    if m in seen: continue
    seen[m] = 0
    for d in sorted(set(x for x in range(2, m+1) if m % x == 0)):
        if d < 13 or d > 30: continue
        pk = perm_power(perm, m // d)
        orb, n = orbits_of_perms([pk])
        if n < 600 or n > 1000: continue
        adjs = quotient_graph(orb, n)
        if adjs is None: continue
        far, diam = far_pairs(adjs)
        print(f"order_g {m} elem_order {d} n {n} far {far} diam {diam} t={time.time()-t0:.0f}", flush=True)
    if time.time() - t0 > 90: break
print("orders seen", sorted(seen), flush=True)
