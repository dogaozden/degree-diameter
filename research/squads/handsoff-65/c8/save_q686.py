import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from quot import *
rng = random.Random(5)
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
want = int(sys.argv[1]); out = sys.argv[2]
for it in range(400):
    g = rand_elem(E, rng, m=rng.randrange(20, 40))
    perm = perm_of(g)
    m = order_of(perm)
    if m % want: continue
    pk = perm_power(perm, m // want)
    orb, n = orbits_of_perms([pk])
    if n != 686: continue
    adjs = quotient_graph(orb, n)
    if adjs is None: continue
    far, diam = far_pairs(adjs)
    print("n", n, "far", far, "diam", diam, "maxdeg", max(len(a) for a in adjs), flush=True)
    write_edges(adjs, out)
    break
