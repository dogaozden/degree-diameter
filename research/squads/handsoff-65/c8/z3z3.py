# search commuting order-3 elements (projective permutations on H(5) vertices) -> quotient by Z3xZ3
import sys, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from quot import *
rng = random.Random(9)
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
t0 = time.time()
o3 = []
seen = set()
while len(o3) < 150 and time.time() - t0 < 200:
    g = rand_elem(E, rng, m=rng.randrange(20, 40))
    perm = perm_of(g)
    m = order_of(perm)
    if m % 3: continue
    a = perm_power(perm, m // 3)
    key = tuple(a[:50])
    if key in seen: continue
    seen.add(key); o3.append(a)
print("order-3 elements:", len(o3), time.time()-t0, flush=True)
def commute(a, b):
    return all(a[b[x]] == b[a[x]] for x in range(0, NV, 7))
pairs = []
for i in range(len(o3)):
    for j in range(i+1, len(o3)):
        if commute(o3[i], o3[j]) and commute(o3[i], o3[j]):
            pairs.append((i, j))
print("commuting pairs (sampled):", len(pairs), time.time()-t0, flush=True)
found = None
for i, j in pairs[:50]:
    a, b = o3[i], o3[j]
    # check group <a,b> has order 9 and is elementary abelian
    ab = [a[b[x]] for x in range(NV)]
    grp = {tuple(range(NV))}
    frontier = [tuple(range(NV))]
    gens = [tuple(a), tuple(b)]
    elems = {tuple(range(NV))}
    stack = [tuple(range(NV))]
    while stack:
        x = stack.pop()
        for gg in gens:
            y = tuple(gg[t] for t in x)
            if y not in elems:
                elems.add(y); stack.append(y)
        if len(elems) > 50: break
    if len(elems) == 9:
        found = (a, b); print("Z3xZ3 found, order", len(elems), flush=True); break
if found:
    a, b = found
    orb, n = orbits_of_perms([a, b])
    adjs = quotient_graph(orb, n)
    far, diam = far_pairs(adjs)
    print("Z3xZ3 quotient n", n, "far", far, "diam", diam, "maxdeg", max(len(x) for x in adjs), flush=True)
    write_edges(adjs, "/home/user/degree-diameter/research/squads/handsoff-65/c8/gh_z3z3.edges")
else:
    print("no Z3xZ3 found", flush=True)
