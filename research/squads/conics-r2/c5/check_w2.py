# c5: check the folding lemma (0.1) and Prop 2.2 (clones + shadows on W(2^(2e+1)), q=2) by brute force.
import itertools, networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

def B(u, v):  # symplectic form on GF(2)^4
    return (u[0]*v[1] + u[1]*v[0] + u[2]*v[3] + u[3]*v[2]) % 2
def add(u, v):
    return tuple((a+b) % 2 for a, b in zip(u, v))

vecs = [tuple((n >> k) & 1 for k in range(4)) for n in range(1, 16)]
lines = sorted({frozenset([u, v, add(u, v)]) for u, v in itertools.combinations(vecs, 2) if B(u, v) == 0}, key=sorted)
assert len(lines) == 15, len(lines)
P = [('p', i) for i in range(15)]
Lx = [('L', j) for j in range(15)]
inc0 = {(P[i], Lx[j]) for i in range(15) for j in range(15) if vecs[i] in lines[j]}
G = nx.Graph()
G.add_nodes_from(P + Lx)
G.add_edges_from((a, b) for a, b in inc0)

# all automorphisms of the incidence graph; keep those swapping points and lines that are involutions
dualities = []
for m in GraphMatcher(G, G).isomorphisms_iter():
    if all(m[x][0] != x[0] for x in P):          # points go to lines
        if all(m[m[x]] == x for x in P + Lx):     # involution
            dualities.append(m)
print("W(2) involutive dualities:", len(dualities))
theta = dualities[0]
absP = [x for x in P if (x, theta[x]) in inc0 or (theta[x], x) in inc0]
absL = [L for L in Lx if (L, theta[L]) in inc0 or (theta[L], L) in inc0]
print("absolute points:", len(absP), " absolute lines:", len(absL))
# each line contains exactly one absolute point (ovoid), each point on exactly one absolute line (spread)
print("ovoid:", all(sum(1 for x in absP if (x, L) in inc0) == 1 for L in Lx))
print("spread:", all(sum(1 for L in absL if (x, L) in inc0) == 1 for x in P))

def fold_check(points, lines_, inc, Theta, label):
    # Lemma 0.1: G_theta vertices = points, p~r iff p!=r and p I Theta(r)
    H = nx.Graph()
    H.add_nodes_from(points)
    for p in points:
        for r in points:
            if p != r and inc(p, Theta[r]):
                H.add_edge(p, r)
    for p in points:
        for r in points:
            if p != r:
                assert inc(p, Theta[r]) == inc(r, Theta[p]), "symmetry"
    deg = max(d for _, d in H.degree())
    print(label, "vertices", H.number_of_nodes(), "maxdeg", deg, "diam", nx.diameter(H) if nx.is_connected(H) else "disconnected")

incf = lambda x, L: (x, L) in inc0
fold_check(P, Lx, incf, theta, "j=0 W(2) folded:")

# Prop 2.2 blow-up: j clones of each absolute point, j shadows over each absolute line
for j in (1, 2):
    pts = P + [('pc', p, c) for p in absP for c in range(1, j+1)]
    lns = Lx + [('Ls', L, c) for L in absL for c in range(1, j+1)]
    def base(x):
        return x[1] if x[0] in ('p', 'pc') else None
    def inc(x, L):
        if x[0] == 'p' and L[0] == 'L':
            return (x, L) in inc0
        if x[0] == 'pc' and L[0] == 'L':
            return (x[1], L) in inc0
        if x[0] == 'p' and L[0] == 'Ls':
            return (x, L[1]) in inc0
        if x[0] == 'pc' and L[0] == 'Ls':
            return (x[1], L[1]) in inc0
        return False
    Th = dict(theta)
    for p in absP:
        for c in range(1, j+1):
            Th[('pc', p, c)] = ('Ls', theta[p], c)
            Th[('Ls', theta[p], c)] = ('pc', p, c)
    # Theta: involution, swaps points and lines, incidence reversed
    assert all(Th[Th[x]] == x for x in pts + lns)
    ok = all(inc(x, L) == inc(Th[L], Th[x]) for x in pts for L in lns)
    print("j=%d self-polar (Theta incidence-preserving):" % j, ok, " |points|", len(pts), " |lines|", len(lns))
    fold_check(pts, lns, inc, Th, "j=%d folded:" % j)
    print("   expected vertices", (3+j)*5, "expected maxdeg", 3+j)
