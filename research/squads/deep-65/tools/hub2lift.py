#!/usr/bin/env python3
"""hub2lift.py (deep-65): write a hub-family graph (S, KA, HB on a group G) as a regular voltage lift by a normal
subgroup N of G that meets KA and HB trivially (so N acts freely on all four orbits).

The base has |G/N| A0-vertices a_i, one A1 hub vertex alpha per N-orbit of A1 (|G/HB|/|N| of them), |G/N| B0-vertices
b_j and the B1 hub vertices beta. Lift convention (as in shared/tabu.c): edge "u w g" with u on side 0 means
(u, h) ~ (w, h g); N acts on the left. Voltages are normalised so that the BFS tree from vertex 0 (built exactly as
tabu.c builds it) has identity voltages.

usage: hub2lift.py TABLE "S" "KA elements" "HB elements" "N elements" OUT.vl OUT.grp
  writes the base with voltages (OUT.vl) and N's multiplication table (OUT.grp, element 0 = identity).
"""
import sys

def load(fn):
    f = open(fn).read().split()
    m = int(f[0]); T = [int(x) for x in f[1:1 + m * m]]
    return m, T

def main():
    tab, Ss, KAs, HBs, Ns, outvl, outgrp = sys.argv[1:8]
    m, T = load(tab)
    mul = lambda x, y: T[x * m + y]
    inv = [0] * m
    for x in range(m):
        for y in range(m):
            if mul(x, y) == 0: inv[x] = y
    S = [int(x) for x in Ss.split()]; KA = [int(x) for x in KAs.split()]; HB = [int(x) for x in HBs.split()]
    N = sorted(int(x) for x in Ns.split()); assert N[0] == 0
    Nset = set(N); nidx = {g: i for i, g in enumerate(N)}
    for a in N:
        for b in N: assert mul(a, b) in Nset
        for g in range(m): assert mul(mul(inv[g], a), g) in Nset   # normal
    assert len(set(KA) & Nset) == 1 and len(set(HB) & Nset) == 1
    # transversal of G/N
    trans, seen = [], set()
    for g in range(m):
        if g in seen: continue
        trans.append(g)
        for n in N: seen.add(mul(n, g))
    q = len(trans)
    cos = {}
    for i, t in enumerate(trans):
        for n in N: cos[mul(n, t)] = i
    def split(x):  # x = n t_i -> (i, n)
        i = cos[x]; return i, mul(x, inv[trans[i]])
    # hubs: B1 = left cosets x KA; A1 = left cosets y HB. Label hub orbits under N.
    def hub_orbits(sub):
        cosets = {}
        for x in range(m):
            key = frozenset(mul(x, k) for k in sub); cosets[key] = 1
        cl = list(cosets)
        # N-orbits on cosets
        orb, reps = {}, []
        for c in cl:
            if c in orb: continue
            r = len(reps); reps.append(c)
            for n in N: orb[frozenset(mul(n, x) for x in c)] = r
        return cl, orb, reps
    clK, orbK, repsK = hub_orbits(KA)
    clH, orbH, repsH = hub_orbits(HB)
    # label of a hub coset c in orbit r: the n with c = n * rep_r
    def hublabel(c, reps, orb):
        r = orb[c]; rep = reps[r]; x0 = min(rep)
        for n in N:
            if frozenset(mul(n, x) for x in rep) == c: return r, n
        raise Exception
    nA1, nB1 = len(repsH), len(repsK)
    # vertices: side 0: a_0..a_{q-1}, alpha_0..; side 1: b_0..b_{q-1}, beta_0..
    va = lambda i: i
    valpha = lambda r: q + r
    vb = lambda j: q + nA1 + j
    vbeta = lambda r: q + nA1 + q + r
    nb = 2 * q + nA1 + nB1
    side = [0] * (q + nA1) + [1] * (q + nB1)
    edges = []  # (u side0, w side1, g in G (element of N))
    # A0-B0: (a_i, n) ~ (b_j, n g), g = t_i s t_j^-1
    for i, t in enumerate(trans):
        for s in S:
            j = cos[mul(t, s)]; g = mul(mul(t, s), inv[trans[j]]); edges.append((va(i), vb(j), g))
    # A0 - B1: for each beta orbit r, hub (beta_r, n) = n * rep_r ; members x = n * y for y in rep_r.
    # y = n_y t_i -> (a_i, n n_y) ~ (beta_r, n): side0 is a_i: (a_i, h) ~ (beta_r, h n_y^-1)
    for r, rep in enumerate(repsK):
        for y in rep:
            i, ny = split(y); edges.append((va(i), vbeta(r), inv[ny]))
    # A1 - B0: hub (alpha_r, n) = n * rep_r; member y = n_y t_j -> (b_j, n n_y): (alpha_r, h) ~ (b_j, h n_y)
    for r, rep in enumerate(repsH):
        for y in rep:
            j, ny = split(y); edges.append((valpha(r), vb(j), ny))
    # tabu.c BFS tree (edge order; adjacency in edge order; BFS from vertex 0)
    adj = [[] for _ in range(nb)]
    for e, (u, w, g) in enumerate(edges):
        adj[u].append((w, e, 0)); adj[w].append((u, e, 1))
    pot = [None] * nb; pot[0] = 0; qu = [0]; h = 0
    # potentials p_v so that new volt = p_u^-1 g p_w (u side0 -> w side1) is identity on tree edges
    while h < len(qu):
        x = qu[h]; h += 1
        for (y, e, d) in adj[x]:
            if pot[y] is None:
                u, w, g = edges[e]
                if d == 0:   # x = u, y = w: need p_u^-1 g p_w = e -> p_w = g^-1 p_u
                    pot[y] = mul(inv[g], pot[x])
                else:        # x = w, y = u: p_u = g p_w
                    pot[y] = mul(g, pot[x])
                qu.append(y)
    assert all(p is not None for p in pot)
    with open(outvl, "w") as f:
        f.write("%d %d\n" % (nb, len(edges)))
        f.write(" ".join(map(str, side)) + "\n")
        for (u, w, g) in edges:
            ng = mul(mul(inv[pot[u]], g), pot[w]); f.write("%d %d %d\n" % (u, w, nidx[ng]))
    with open(outgrp, "w") as f:
        f.write("%d\n" % len(N))
        for a in N: f.write(" ".join(str(nidx[mul(a, b)]) for b in N) + "\n")
    print("base vertices %d (A0 %d, A1 %d, B0 %d, B1 %d), edges %d, |N| %d -> lift order %d" % (nb, q, nA1, q, nB1, len(edges), len(N), nb * len(N)))

main()
