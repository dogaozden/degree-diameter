"""Typed level graph with RELAXED freed line sets on the D->H arcs (Proposition 7.3 of D5_QUADRANGLE.md).

Same layout as build_typed.py (G = Q(4,q) = W(q)^D, rotational tournament, types HHHDHHD, ovoid O on H->D arcs, two-point
local dualities on non-friendly arcs).  On a D->H arc j -> j' the freed set is a relaxed set T of lines of G (points of
W(q)): every line of T meets at most one other line m of T, at a point z not in O.  Hub rule: the B-hub at the slot
(l, j->j') sits, in level j', at the slot of the ovoid point o_m of the partner m (freed on the H->D arc out of j');
the A-hub at the B-slot (l, j') sits, in level j, at a B-slot at o_m (freed on an H->D arc into j).

usage: python3 build_relaxed.py q T.json T2.json out_prefix      (T2 is used on the arc 6->2 instead of T)
"""
import sys, json, random, os
import numpy as np
from gqlib import W, regular_spread_W, is_partial_ovoid
from levels import build, write_edges, apsp, rotational_arcs
from localdual import local_duality_pair, pick_pair
from hubopt import hub_D0, search


def partners(G, T, O):
    Ts = set(T); Oset = set(O); P = {}
    for l in T:
        ms = [m for m in T if m != l and G.con[l, m]]
        assert len(ms) <= 1, ('line with two partners', l, ms)
        if ms:
            m = ms[0]
            z = (set(G.lines[l]) & set(G.lines[m])).pop()
            assert z not in Oset, ('meeting point on the ovoid', l, m)
            om = [p for p in G.lines[m] if p in Oset]
            assert len(om) == 1
            P[l] = (m, om[0])
    return P


def main():
    q = int(sys.argv[1]); T = sorted(json.load(open(sys.argv[2]))); T2 = sorted(json.load(open(sys.argv[3]))); out = sys.argv[4]
    r = 3; types = 'HHHDHHD'; L = 7; arcs = rotational_arcs(L)
    Wq = W(q); G = Wq.dual('Q(4,%d)' % q); N = G.np
    O = regular_spread_W(Wq)
    PT = partners(G, T, O); PT2 = partners(G, T2, O)
    # level 6 has 3 D->H out-arcs but only 2 H->D in-arcs: ovoid points demanded via T and T2 must be disjoint
    oT = {om for (_, om) in PT.values()}; oT2 = {om for (_, om) in PT2.values()}
    # (with A-hubs following a line across levels, T2 = T is allowed)
    M, R, Tof = {}, {}, {}
    for (u, v) in arcs:
        M[(u, v)] = list(range(N))
        if types[u] == 'H' and types[v] == 'D':
            R[(u, v)] = set(O)
        elif types[u] == 'D' and types[v] == 'H':
            Tt = T2 if (u, v) == (6, 2) else T
            R[(u, v)] = set(Tt); Tof[(u, v)] = PT2 if (u, v) == (6, 2) else PT
        else:
            Hq = G if types[u] == 'H' else Wq
            avoid = O if types[u] == 'H' else sorted(set(T) | set(T2))
            x, y, l, m = pick_pair(Hq, avoid_pts=avoid)
            M[(u, v)] = local_duality_pair(Hq, x, y, l, m); R[(u, v)] = {x, y}
    Aslots = {j: [] for j in range(L)}; Bslots = {j: [] for j in range(L)}
    for (u, v) in arcs:
        for a in sorted(R[(u, v)]):
            Aslots[u].append((u, a, (u, v))); Bslots[v].append((v, M[(u, v)][a], (u, v)))
    KB = min(len(Aslots[j]) for j in range(L)); KA = min(len(Bslots[j]) for j in range(L))
    print('alpha', [len(Aslots[j]) for j in range(L)], 'beta', [len(Bslots[j]) for j in range(L)], 'K_B', KB, 'K_A', KA,
          '|T|', len(T), '|T2|', len(T2), 'pairs', len(PT) // 2, len(PT2) // 2)
    hd_out = {j: next((u, v) for (u, v) in arcs if u == j and types[v] == 'D') for j in range(L) if types[j] == 'H'}
    # ---- B-hubs
    req = []                           # per hub: dict level -> slot
    Dlev = [j for j in range(L) if types[j] == 'D']
    order = {}
    for d in Dlev:
        con = [s for s in Aslots[d] if s[2] in Tof and s[1] in Tof[s[2]]]
        rest = [s for s in Aslots[d] if s not in con]
        assert len(con) <= KB
        order[d] = con + rest
    Bhubs = []
    used = set()
    for i in range(KB):
        h = {}
        for d in Dlev:
            s = order[d][i]; h[d] = s
            if s[2] in Tof and s[1] in Tof[s[2]]:
                m, om = Tof[s[2]][s[1]]; jt = s[2][1]
                t2 = hd_out[jt]
                need = (jt, om, t2)
                assert need in Aslots[jt] and jt not in h
                h[jt] = need
        Bhubs.append(h)
    for h in Bhubs:
        for s in h.values():
            assert s not in used, ('B-slot demanded twice', s); used.add(s)
    for j in range(L):
        pool = [s for s in Aslots[j] if s not in used]
        for h in Bhubs:
            if j not in h:
                h[j] = pool.pop(0); used.add(h[j])
    # ---- A-hubs: one A-hub per (D-level d, partnered line l) takes the B-slots (l, d->j') in ALL H-levels j' fed by d
    # (they all ask for the ovoid point o_m in level d, so one B-slot of level d serves them all)
    Hlev = [j for j in range(L) if types[j] == 'H']
    groups = {d: {} for d in Dlev}
    for jp in Hlev:
        for s in Bslots[jp]:
            t = s[2]
            if t in Tof and s[1] in Tof[t]:
                groups[t[0]].setdefault(s[1], []).append(s)
    Ahubs = [dict() for _ in range(KA)]
    usedB = set()
    for d in Dlev:
        items = sorted(groups[d].items())
        assert len(items) <= KA, ('too many partnered lines', d, len(items), KA)
        for i, (l, slots) in enumerate(items):
            g = Ahubs[i]
            for s in slots:
                assert s[0] not in g; g[s[0]] = s; usedB.add(s)
            m, om = Tof[slots[0][2]][l]
            assert all(Tof[s[2]][l][1] == om for s in slots)
            copies = [c for c in Bslots[d] if c[1] == om and c not in usedB]
            assert copies, ('no free B-slot at the ovoid point', d, om)
            assert d not in g; g[d] = copies[0]; usedB.add(copies[0])
    for j in range(L):
        pool = [s for s in Bslots[j] if s not in usedB]
        for g in Ahubs:
            if j not in g:
                g[j] = pool.pop(0); usedB.add(g[j])
    Bh = [[h[j] for j in range(L)] for h in Bhubs]
    Ah = [[g[j] for j in range(L)] for g in Ahubs]
    n0, E0 = build(G, types, M, R, Bh, Ah, [], arcs=arcs)
    nv = L * 2 * N
    D0 = hub_D0(n0, E0, list(range(nv, nv + KB + KA)))
    for sd in range(int(os.environ.get('HUBSEEDS', '6'))):
        Y, cost = search(D0, KB, KA, q - r, seed=sd, iters=int(os.environ.get('HUBITERS', '6000')))
        print('  hub search seed', sd, 'bad', cost)
        if cost == 0: break
    if cost:
        print('no hub graph'); return
    n, E = build(G, types, M, R, Bh, Ah, Y, arcs=arcs)
    write_edges(out + '.edges', n, E)
    json.dump(dict(q=q, r=r, types=types, arcs=arcs, ovoid_Q4=O, T=T, T2=T2, K_B=KB, K_A=KA,
                   Bhub_slots=Bh, Ahub_slots=Ah, Y=Y,
                   nonfriendly={'%d,%d' % t: dict(R=sorted(R[t]), M=M[t]) for t in arcs if types[t[0]] == types[t[1]]},
                   note='G = Q(4,q) = gqlib.W(q).dual(); friendly matchings = identity; slots (level, element, arc)'),
              open(out + '.json', 'w'), default=int)
    print(apsp(out + '.edges', q + 1 + r, 5, threads=2))


if __name__ == '__main__':
    main()
