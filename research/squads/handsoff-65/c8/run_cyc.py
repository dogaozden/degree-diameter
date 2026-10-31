import sys, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from quot import *
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
t0 = time.time()
stats = {}
for it in range(int(sys.argv[2]) if len(sys.argv) > 2 else 30):
    g = rand_elem(E, rng)
    perm = perm_of(g)
    m = order_of(perm)
    # all powers g^k with cyclic subgroup orders in target range
    for d in sorted(set(x for x in range(2, m+1) if m % x == 0)):
        k = m // d
        pk = perm_power(perm, k)     # element of order d
        orb, n = orbits_of_perms([pk])
        if n < 300 or n > 1600: continue
        adjs = quotient_graph(orb, n)
        if adjs is None: continue
        far, diam = far_pairs(adjs)
        stats.setdefault(d, []).append((n, far, diam))
        print(f"it {it} order_g {m} elem_order {d} n_orbits {n} maxdeg {max(len(a) for a in adjs)} far_pairs {far} diam {diam} t={time.time()-t0:.0f}", flush=True)
        if far == 0 and n > 684:
            write_edges(adjs, f"/home/user/degree-diameter/research/squads/handsoff-65/c8/cand_{n}_{it}_{d}.edges")
            print("CANDIDATE FOUND", n, flush=True)
print({k: sorted(v)[:3] for k, v in stats.items()})
