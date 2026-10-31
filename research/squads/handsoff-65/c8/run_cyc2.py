import sys, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from quot import *
rng = random.Random(int(sys.argv[1]))
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
iters = int(sys.argv[2])
t0 = time.time()
res = {}
for it in range(iters):
    g = rand_elem(E, rng, m=rng.randrange(20, 40))
    perm = perm_of(g)
    m = order_of(perm)
    for d in (7, 8, 9, 10, 12, 6):
        if m % d: continue
        pk = perm_power(perm, m // d)
        orb, n = orbits_of_perms([pk])
        if n < 687 or n > 1000: continue
        adjs = quotient_graph(orb, n)
        if adjs is None: continue
        far, diam = far_pairs(adjs)
        key = d
        res.setdefault(d, []).append(far)
        print(f"it {it} order {d} n {n} far {far} diam {diam} t={time.time()-t0:.0f}", flush=True)
        if far < 3000:
            write_edges(adjs, f"/home/user/degree-diameter/research/squads/handsoff-65/c8/gh_n{n}_far{far}_o{d}_{it}.edges")
    if time.time() - t0 > 400: break
print({k: (len(v), min(v)) for k, v in res.items()}, flush=True)
