"""Other ways to split the Coxeter diagram (BUILDINGS.md §4): for every partition S = J1 | J2 (both non-empty) of the
types A2..A6, B2..B5, D4, D5, F4, G2, the bipartite graph of J1-residues vs J2-residues (adjacent iff they share a
chamber; the intersection is again a single chamber since J1 and J2 are disjoint) has, with all parameters q:
  degrees ~ q^a2 and q^a1 (a_i = N(W_Ji) = length of the longest element of W_Ji),
  order  ~ q^(N - min(a1, a2)),
  diameter D = max block distance (computed over all of W exactly as in weyl_dist.py, blocks = W_J1, W_J2).
The Moore bound with max degree ~ q^max(a) is ~ q^(max(a) (D-1)); the 'gap' max(a)(D-1) - (N - min(a)) >= 0 is the
power of q lost.  gap = 0 is necessary for a family with order/Moore bounded away from 0 as q grows."""
import sys, itertools
sys.path.insert(0, '.')
from weyl_dist import cartan, weyl

def run(t, n):
    C = cartan(t, n); s = weyl(C); rho = tuple([1] * n)
    # all elements with their lengths
    L = {rho: 0}; fr = [rho]
    while fr:
        nf = []
        for lam in fr:
            for i in range(n):
                if lam[i] > 0:
                    mu = s(i, lam)
                    if mu not in L: L[mu] = L[lam] + 1; nf.append(mu)
        fr = nf
    N = max(L.values())
    def longest(J):
        # length of longest element of W_J = size of orbit-BFS depth of rho under J
        seen = {rho: 0}; fr = [rho]; d = 0
        while fr:
            nf = []
            for lam in fr:
                for i in J:
                    mu = s(i, lam)
                    if mu not in seen: seen[mu] = seen[lam] + 1; nf.append(mu)
            fr = nf
        return max(seen.values())
    def orbit(lam, J):
        seen = {lam}; fr = [lam]
        while fr:
            nf = []
            for x in fr:
                for i in J:
                    y = s(i, x)
                    if y not in seen: seen.add(y); nf.append(y)
            fr = nf
        return seen
    res = []
    nodes = list(range(n))
    colour = None
    for k in range(1, n):
        for J1 in itertools.combinations(nodes, k):
            J2 = tuple(x for x in nodes if x not in J1)
            if J1 > J2: continue
            a1, a2 = longest(J1), longest(J2)
            D = 0
            for Js in ((J1, J2), (J2, J1)):
                lev = {}; frn = []
                for x in orbit(rho, Js[0]):
                    lev[x] = 1; frn.append(x)
                m = 1
                while frn:
                    m += 1; K = Js[(m - 1) % 2]; nf = []
                    for lam in frn:
                        for x in orbit(lam, K):
                            if x not in lev: lev[x] = m; nf.append(x)
                    frn = nf
                for lam, mm in lev.items():
                    # distance to same-type vertex / other-type vertex (as in weyl_dist): d = m - [type of m-th block == target]
                    Jm = 0 if mm % 2 == 1 else 1
                    for Kt in (0, 1):
                        d = mm - (1 if Jm == Kt else 0)
                        D = max(D, d)
            gap = max(a1, a2) * (D - 1) - (N - min(a1, a2))
            is_colour = all(C[i][j] == 0 for J in (J1, J2) for i in J for j in J if i != j)
            res.append((gap, J1, J2, a1, a2, D, is_colour))
    print(f"{t}{n}: |W|={len(L)} N={N}; {len(res)} partitions; gap = 0 for: "
          + (", ".join(f"{J1}|{J2} (a={a1},{a2}, D={D}{', colour classes' if c else ''})" for g, J1, J2, a1, a2, D, c in res if g == 0) or "none")
          + f"; smallest gap among non-colour partitions: {min((g for g, *_, c in res if not c), default=None)}")
    return res
for t, n in [('A', 2), ('A', 3), ('A', 4), ('A', 5), ('A', 6), ('B', 2), ('B', 3), ('B', 4), ('B', 5), ('D', 4), ('D', 5), ('F', 4), ('G', 2)]:
    run(t, n)
