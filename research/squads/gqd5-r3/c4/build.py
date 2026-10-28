"""Card r3c4: independent small-q test of Proposition 7.2 (only the A-hub condition), research/theorems/D5_QUADRANGLE.md.

Layout: G = Q4(q) = W(q).dual(), 5 levels, types H H D H D, rotational tournament j -> j+1, j+2 (mod 5), r = 2, degree q+3.
  H->D arcs 0->2, 1->2, 3->4 free the ovoid O (q^2+1 points, regular spread of W(q)).
  D->H arcs 2->3, 4->0, 4->1 free a relaxed set T of lines of G (every line meets at most one other line of T; the meeting
  point is not on O).  Identity matchings on all friendly arcs.
  Non-friendly arcs 0->1, 1->3, 3->0 (H->H, on G) and 2->4 (D->D, on W(q)) carry a two-point local duality (localdual.py)
  and free two elements each.
Hubs: B-hubs (one A-slot per level) are arbitrary.  A-hubs: for every partnered line l (partner m, ovoid point o_m) one
A-hub g_l takes the B-slots (l, 4->0) at level 0, (l, 4->1) at level 1, (l, 2->3) at level 3, and the B-slots at o_m in
levels 2 and 4 (the level-2 slot is the copy from 0->2, the level-4 slot from 3->4).  This is the rule of Proposition 7.2
(the hub of the slot (l,t) sits, in the D-level of t, at o_m).  Other A-hubs are arbitrary.  Hub graph Y: degree q - r,
annealed with hubopt.py so that same-colour hubs are at distance <= 4.

usage: python3 build.py q T_file out_prefix mode seed
  mode = rule     : Proposition 7.2 A-hub rule holds (expected: valid, D = 5)
  mode = break4   : the A-hub of the first partnered line gets, at level 4 (its D-level), a free B-slot at a point NOT on m
  mode = break2   : same, but the moved slot is at level 2 (the D-level of the arc 2->3)
  mode = norule   : no A-hub rule at all (all A-hubs arbitrary)
"""
import sys, json, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, Q4, regular_spread_W, is_partial_ovoid
from levels import build, write_edges, apsp, rotational_arcs
from localdual import local_duality_pair, pick_pair
from hubopt import hub_D0, search

L = 5
types = 'HHDHD'
arcs = rotational_arcs(L)                          # (0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(3,0),(4,0),(4,1)
HD = [(0, 2), (1, 2), (3, 4)]
DH = [(2, 3), (4, 0), (4, 1)]
NF = [(0, 1), (1, 3), (3, 0), (2, 4)]


def main():
    q = int(sys.argv[1]); Tfile = sys.argv[2]; out = sys.argv[3]; mode = sys.argv[4]; seed = int(sys.argv[5])
    r = (L - 1) // 2
    assert r == 2 and types == 'HHDHD' and len(arcs) == 10
    rng = random.Random(seed)
    Wq = W(q); G = Q4(q); N = G.np
    O = sorted(regular_spread_W(Wq)); Oset = set(O)
    assert len(O) == q * q + 1 and is_partial_ovoid(G, O)
    T = sorted(int(x) for x in open(Tfile).read().split()[1:])
    # ---- partner structure of T (Section 7): each line meets at most one other line of T, at a point off O
    P = {}
    for l in T:
        ms = [m for m in T if m != l and G.con[l, m]]
        assert len(ms) <= 1, ('line meets two others', l, ms)
        if ms:
            m = ms[0]
            z = set(G.lines[l]) & set(G.lines[m]); assert len(z) == 1
            z = z.pop(); assert z not in Oset, 'meeting point on the ovoid'
            om = [p for p in G.lines[m] if p in Oset]; assert len(om) == 1
            P[l] = (m, om[0])
    pairs = len(P) // 2
    print('|T| =', len(T), 'partnered lines =', len(P), 'pairs =', pairs, flush=True)
    # ---- transitions
    M, R = {}, {}
    for (u, v) in arcs:
        if (u, v) in HD:
            M[(u, v)] = list(range(N)); R[(u, v)] = set(O)
        elif (u, v) in DH:
            M[(u, v)] = list(range(N)); R[(u, v)] = set(T)
        else:
            Hq = G if types[u] == 'H' else Wq
            avoid = O if types[u] == 'H' else T
            x, y, l, m = pick_pair(Hq, avoid_pts=avoid)
            M[(u, v)] = local_duality_pair(Hq, x, y, l, m); R[(u, v)] = {x, y}
    # ---- slots: A-slot (j, a, t) of level j = freed A-element; B-slot (j, b, t) of level j = b = M_t(a)
    Aslots = {j: [] for j in range(L)}; Bslots = {j: [] for j in range(L)}
    for t in arcs:
        u, v = t
        for a in sorted(R[t]):
            Aslots[u].append((u, a, t)); Bslots[v].append((v, M[t][a], t))
    KB = min(len(Aslots[j]) for j in range(L)); KA = min(len(Bslots[j]) for j in range(L))
    print('alpha', [len(Aslots[j]) for j in range(L)], 'beta', [len(Bslots[j]) for j in range(L)],
          'K_B', KB, 'K_A', KA, flush=True)
    # ---- B-hubs: arbitrary (no rule)
    Bh = [[Aslots[j][i] for j in range(L)] for i in range(KB)]
    # ---- A-hubs
    used = set()
    def take(s):
        assert s not in used, ('B-slot used twice', s); used.add(s)
    Ah = []
    rule_hubs = []
    if mode != 'norule':
        for l in sorted(P):
            m, om = P[l]
            g = {0: (0, l, (4, 0)), 1: (1, l, (4, 1)), 3: (3, l, (2, 3)), 2: (2, om, (0, 2)), 4: (4, om, (3, 4))}
            for s in g.values(): take(s)
            Ah.append(g); rule_hubs.append(l)
    assert len(Ah) <= KA, ('too many partnered lines for K_A', len(Ah), KA)
    if mode in ('break4', 'break2'):
        l0 = rule_hubs[0]; m0, om0 = P[l0]
        lev = 4 if mode == 'break4' else 2
        g = Ah[0]
        off_m = set(G.lines[m0])
        free = [s for s in Bslots[lev] if s not in used and s[1] not in off_m]
        assert free, 'no free off-partner slot at this level'
        old = g[lev]; used.discard(old)
        g[lev] = free[0]; take(free[0])
        print('broke rule for line', l0, 'partner', m0, 'ovoid point', om0,
              ': level', lev, 'slot', old, '->', free[0], flush=True)
    # remaining A-hubs (arbitrary): create the empty hubs first, then fill every level
    while len(Ah) < KA:
        Ah.append({})
    for j in range(L):
        pool = [s for s in Bslots[j] if s not in used]
        rng.shuffle(pool)
        for g in Ah:
            if j not in g:
                g[j] = pool.pop(0); used.add(g[j])
    assert all(sorted(g.keys()) == list(range(L)) for g in Ah) and len(Ah) == KA
    # ---- hub graph
    Bhl = [list(h) for h in Bh]; Ahl = [[g[j] for j in range(L)] for g in Ah]
    n0, E0 = build(G, types, M, R, Bhl, Ahl, [], arcs=arcs)
    nv = L * 2 * N
    D0 = hub_D0(n0, E0, list(range(nv, nv + KB + KA)))
    best = None
    for sd in range(8):
        Y, cost = search(D0, KB, KA, q - r, seed=sd + 100 * seed, iters=20000)
        print('  hub search seed', sd, 'bad', cost, flush=True)
        if best is None or cost < best[1]: best = (Y, cost)
        if cost == 0: break
    Y, cost = best
    if cost:
        print('no hub graph satisfying (HG)', flush=True)
    Bhl = [[s for s in h] for h in Bh]; Ahl = [[g[j] for j in range(L)] for g in Ah]
    n, E = build(G, types, M, R, Bhl, Ahl, Y, arcs=arcs)
    write_edges(out + '.edges', n, E)
    json.dump(dict(q=q, r=r, types=types, arcs=arcs, mode=mode, T=T, O=O, K_B=KB, K_A=KA, n=n, hub_bad=cost,
                   partners={str(k): v for k, v in P.items()}, Bhubs=Bhl, Ahubs=Ahl, Y=Y,
                   M={'%d,%d' % t: list(map(int, M[t])) for t in arcs}, R={'%d,%d' % t: sorted(map(int, R[t])) for t in arcs}),
              open(out + '.json', 'w'), default=int)
    print('n =', n, 'hub_bad =', cost, flush=True)
    print('D=5:', apsp(out + '.edges', q + 1 + r, 5), flush=True)
    print('D=6:', apsp(out + '.edges', q + 1 + r, 6), flush=True)


if __name__ == '__main__':
    main()
