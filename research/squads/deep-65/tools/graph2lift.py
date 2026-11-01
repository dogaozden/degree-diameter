#!/usr/bin/env python3
"""graph2lift.py (deep-65): write a bipartite graph as a regular voltage lift by a subgroup N of its automorphism
group that acts semiregularly (freely) on the vertices.

Input: the edge list (first line n, then "u v") and dreadnaut's generator output (cycle notation lines). The group
generated is enumerated as permutations; N = the elements whose order divides ORD (default 7) must form a subgroup of
order |N| that acts freely; then base vertices = N-orbits, voltages from the action. Output: vl file (as shared/tabu.c
and shared/kopt.c read it, tree voltages normalised to the identity exactly as tabu.c builds its BFS tree) and N's table.
Lift convention: edge "u w g" (u on side 0) means (u, h) ~ (w, h g); N acts on the left.

usage: graph2lift.py EDGES DREADNAUT_OUTPUT ORD OUT.vl OUT.grp
"""
import re, sys

def main():
    edges_fn, dre_fn, ORD, outvl, outgrp = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
    f = open(edges_fn); n = int(f.readline()); E = [tuple(map(int, l.split())) for l in f if len(l.split()) >= 2]
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    # bipartition by BFS
    side = [-1] * n; side[0] = 0; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if side[y] < 0: side[y] = 1 - side[x]; st.append(y)
    # generators from dreadnaut output ("Gen(M) #k: (cycles)", continuation lines indented); first block only
    txt = open(dre_fn).read()
    i0 = txt.index('Gen'); i1 = txt.index('Level', i0)
    gens = [g for g in re.split(r'Gen\([^)]*\) #\d+:', txt[i0:i1]) if '(' in g]
    perms = []
    for g in gens:
        p = list(range(n))
        for cyc in re.findall(r'\(([^)]*)\)', g):
            c = list(map(int, cyc.split()))
            for i in range(len(c)): p[c[i]] = c[(i + 1) % len(c)]
        perms.append(tuple(p))
    ident = tuple(range(n))
    comp = lambda a, b: tuple(a[b[i]] for i in range(n))   # a o b (apply b first)
    group = {ident}; frontier = [ident]
    while frontier:
        nxt = []
        for g in frontier:
            for p in perms:
                h = comp(p, g)
                if h not in group: group.add(h); nxt.append(h)
        frontier = nxt
    def order(g):
        k, h = 1, g
        while h != ident: h = comp(g, h); k += 1
        return k
    N = [g for g in group if ORD % order(g) == 0]
    N.sort(key=lambda g: g != ident)
    idx = {g: i for i, g in enumerate(N)}
    for a in N:
        for b in N: assert comp(a, b) in idx, "elements of order dividing ORD do not form a subgroup"
    for g in N[1:]:
        assert all(g[i] != i for i in range(n)), "N does not act freely"
    print("|Aut| %d, |N| %d" % (len(group), len(N)))
    # base vertices: N-orbits, side-0 orbits first; representative = min
    seen = [-1] * n; reps = []
    for s in (0, 1):
        for x in range(n):
            if side[x] == s and seen[x] < 0:
                b = len(reps); reps.append(x)
                for g in N: seen[g[x]] = b
    nb = len(reps); bside = [side[r] for r in reps]
    # label of vertex: x = g(rep) -> (base, g)
    lab = {}
    for b, r in enumerate(reps):
        for g in N: lab[g[r]] = (b, idx[g])
    inv = [0] * len(N)
    for i, a in enumerate(N):
        for j, b in enumerate(N):
            if comp(a, b) == ident: inv[i] = j
    mul = [[idx[comp(a, b)] for b in N] for a in N]
    # base edges with voltages: from each side-0 rep r (label (b, e)): neighbour y = (w, v)
    bedges = []
    for b, r in enumerate(reps):
        if bside[b] != 0: continue
        for y in adj[r]:
            w, v = lab[y]; bedges.append((b, w, v))
    # tabu.c spanning tree and normalisation
    badj = [[] for _ in range(nb)]
    for e, (u, w, g) in enumerate(bedges): badj[u].append((w, e, 0)); badj[w].append((u, e, 1))
    pot = [None] * nb; pot[0] = 0; qu = [0]; h = 0
    while h < len(qu):
        x = qu[h]; h += 1
        for (y, e, d) in badj[x]:
            if pot[y] is None:
                u, w, g = bedges[e]
                pot[y] = mul[inv[g]][pot[x]] if d == 0 else mul[g][pot[x]]
                qu.append(y)
    with open(outvl, 'w') as f:
        f.write("%d %d\n%s\n" % (nb, len(bedges), " ".join(map(str, bside))))
        for (u, w, g) in bedges: f.write("%d %d %d\n" % (u, w, mul[mul[inv[pot[u]]][g]][pot[w]]))
    with open(outgrp, 'w') as f:
        f.write("%d\n" % len(N))
        for row in mul: f.write(" ".join(map(str, row)) + "\n")
    print("base %d vertices, %d edges -> %s" % (nb, len(bedges), outvl))

main()
