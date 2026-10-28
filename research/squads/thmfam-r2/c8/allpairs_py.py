# Own all-pairs diameter of the component of (I,A) in H(PGL(2,q), psi(S_p)) (no lab code), sanity cross-check for item (7).
import sys
from collections import deque
import qlib as L
p, q = int(sys.argv[1]), int(sys.argv[2])
x, y = L.xy_solutions(q)[0]
Sm = [L.psi(a, x, y, q) for a in L.lps_set(p)]
d = L.haar_component(Sm, q)
verts = list(d.keys()); idx = {v: i for i, v in enumerate(verts)}
adjs = [L.madj(M, q) for M in Sm]
nb = [[] for _ in verts]
for v in verts:
    g, side = v
    if side == 'A':
        w = [(L.pnorm(L.mm(M, g, q), q), 'B') for M in Sm]
    else:
        w = [(L.pnorm(L.mm(Mi, g, q), q), 'A') for Mi in adjs]
    nb[idx[v]] = [idx[u] for u in w]
# symmetry check of the adjacency we built
sym = all(idx_v in nb[u] for v_i, lst in enumerate(nb) for u, idx_v in [(u, v_i) for u in lst])
diam = 0
for s in range(len(verts)):
    dist = [-1] * len(verts); dist[s] = 0; dq = deque([s])
    while dq:
        v = dq.popleft()
        for u in nb[v]:
            if dist[u] < 0:
                dist[u] = dist[v] + 1; dq.append(u)
    assert min(dist) >= 0
    diam = max(diam, max(dist))
print("p=%d q=%d x=%d y=%d vertices=%d degree=%d symmetric=%s allpairs_diameter=%d" % (p, q, x, y, len(verts), len(nb[0]), sym, diam))
