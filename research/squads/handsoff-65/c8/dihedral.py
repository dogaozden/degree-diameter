# find dihedral subgroups <g,t> (t g t = g^-1) of H(5)'s automorphism group; quotient and score
import sys, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from quot import *
rng = random.Random(int(sys.argv[1]))
want_g = int(sys.argv[2])     # order of cyclic part
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
t0 = time.time()
gs = []; ts = []
tries = 0
while time.time() - t0 < 80 and (len(gs) < 6 or len(ts) < 600):
    g = rand_elem(E, rng, m=rng.randrange(20, 40))
    perm = perm_of(g)
    m = order_of(perm)
    if m % want_g == 0 and len(gs) < 6:
        gs.append(perm_power(perm, m // want_g))
    if m % 2 == 0 and len(ts) < 600:
        ts.append(perm_power(perm, m // 2))
print("g elems", len(gs), "involutions", len(ts), flush=True)
def inv(p):
    r = [0]*NV
    for i, x in enumerate(p): r[x] = i
    return r
def comp(a, b):  # a after b
    return [a[b[x]] for x in range(NV)]
found = []
for gi, gg in enumerate(gs):
    gin = inv(gg)
    for t in ts:
        # t g t == g^-1 on all vertices
        if all(comp(t, comp(gg, t))[x] == gin[x] for x in range(0, NV, 3)):
            found.append((gi, t)); break
    if found and found[-1][0] == gi: pass
print("dihedral pairs found:", len(found), flush=True)
for gi, t in found[:3]:
    gg = gs[gi]
    orb, n = orbits_of_perms([gg, t])
    adjs = quotient_graph(orb, n)
    if adjs is None:
        print("bad orbit", flush=True); continue
    far, diam = far_pairs(adjs)
    print(f"D{want_g} (order {2*want_g}) quotient n {n} far {far} diam {diam} maxdeg {max(len(a) for a in adjs)}", flush=True)
    if n > 684 and far < 13000:
        write_edges(adjs, f"/home/user/degree-diameter/research/squads/handsoff-65/c8/dih{want_g}_n{n}_far{far}.edges")
