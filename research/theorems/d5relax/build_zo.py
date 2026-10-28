"""Seven-level graph HHHDHHD over Q(4,q) with a relaxed set T on the D->H arcs, partner pairs allowed to meet at ovoid
points (Lemma 7.3 of D5_QUADRANGLE.md, job d5-relax).

Layout as in D5_QUADRANGLE.md section 11: G = Q(4,q) = gqlib.W(q).dual(), rotational tournament on Z_7, types HHHDHHD,
M = id and R = O (the ovoid of Lemma 1.1) on the five H->D arcs, M = id and R = T on the five D->H arcs, two-point local
dualities (Proposition 6.4) on the eleven non-friendly arcs.  Hubs:
  A-hub g_l for every line l of T takes the B-slots (l, t) of the five D->H arcs t (levels 4, 5, 0, 1, 2); if l has a
  partner m, it takes in level 3 and in level 6 a B-slot at the point o_m of O on m (Lemma 7.3: a point of O carries
  three free B-slots in level 3 and two in level 6, and at most two hubs ask for it).  The other K_A - |T| A-hubs and
  the B-hubs take free slots in order (no condition).  Y: random bipartite graph of maximum degree q - r, then
  double-edge swaps until same-colour hubs are within distance 4 (hubopt.py, level paths counted).
Option BREAK=1 moves the level-3 slot of one hub of a pair meeting at an ovoid point off its partner (negative control).

usage: python3 build_zo.py q T.json out_prefix [seed]     (T: points of W(q) = lines of Q(4,q); json list or rtabu file)
writes out_prefix.json (solution file, readable by d5gq/sol2edges.py) and out_prefix.edges"""
import sys, os, json, random
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'd5gq'))
from gqlib import W, regular_spread_W
from levels import build, write_edges, rotational_arcs
from localdual import local_duality_pair, pick_pair
from hubopt import hub_D0, search


def load_set(path):
    s = open(path).read().strip()
    if s.startswith('[') or s.startswith('{'):
        T = json.loads(s); return sorted(T['T'] if isinstance(T, dict) else T)
    return sorted(int(x) for x in s.split()[1:])


def partners(G, T, O):
    """partner map l -> (m, z, o_m) of a relaxed set T of lines of G; no condition on z"""
    Oset = set(O); P = {}
    for l in T:
        ms = [m for m in T if m != l and G.con[l, m]]
        assert len(ms) <= 1, ('line with two partners', l, ms)
        if ms:
            m = ms[0]; z = (set(G.lines[l]) & set(G.lines[m])).pop()
            om = [p for p in G.lines[m] if p in Oset]; assert len(om) == 1
            P[l] = (m, z, om[0])
    return P


def main():
    q = int(sys.argv[1]); T = load_set(sys.argv[2]); out = sys.argv[3]
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1; rng = random.Random(seed)
    brk = os.environ.get('BREAK') == '1'
    r = 3; types = 'HHHDHHD'; L = 7; arcs = rotational_arcs(L)
    Wq = W(q); G = Wq.dual(); N = G.np
    O = regular_spread_W(Wq); Oset = set(O)
    PT = partners(G, T, O)
    zO = sorted(l for l, (m, z, om) in PT.items() if z in Oset)
    print('q=%d |T|=%d pairs=%d, pairs meeting at an ovoid point: %d' % (q, len(T), len(PT) // 2, len(zO) // 2))
    M, R = {}, {}
    for (u, v) in arcs:
        if types[u] != types[v]:
            M[(u, v)] = list(range(N)); R[(u, v)] = set(O) if types[u] == 'H' else set(T)
        else:
            Hq = G if types[u] == 'H' else Wq
            x, y, l, m = pick_pair(Hq, avoid_pts=(O if types[u] == 'H' else T))
            M[(u, v)] = local_duality_pair(Hq, x, y, l, m); R[(u, v)] = {x, y}
    Aslots = {j: [] for j in range(L)}; Bslots = {j: [] for j in range(L)}
    for (u, v) in arcs:
        for a in sorted(R[(u, v)]):
            Aslots[u].append((u, a, (u, v))); Bslots[v].append((v, M[(u, v)][a], (u, v)))
    KB = min(len(Aslots[j]) for j in range(L)); KA = min(len(Bslots[j]) for j in range(L))
    print('alpha', [len(Aslots[j]) for j in range(L)], 'beta', [len(Bslots[j]) for j in range(L)], 'K_B', KB, 'K_A', KA,
          'order', L * 2 * N + KB + KA)
    DH = [(u, v) for (u, v) in arcs if types[u] == 'D' and types[v] == 'H']
    Dlev = [j for j in range(L) if types[j] == 'D']
    assert KA >= len(T)
    # ---- A-hubs
    Ah = [dict() for _ in range(KA)]; usedB = set()
    def take(g, s):
        assert s in Bslots[s[0]] and s not in usedB and s[0] not in Ah[g], s
        Ah[g][s[0]] = s; usedB.add(s)
    broken = None
    for i, l in enumerate(T):
        for t in DH:
            take(i, (t[1], l, t))
        if l in PT:
            m, z, om = PT[l]
            for d in Dlev:
                cand = [s for s in Bslots[d] if s[1] == om and s not in usedB]
                if brk and broken is None and l in zO and d == 3:
                    cand = [s for s in Bslots[d] if s[1] not in G.lines[m] and s not in usedB]; broken = (l, m)
                assert cand, ('no free B-slot at the ovoid point', d, om)
                take(i, cand[0])
    for j in range(L):
        pool = [s for s in Bslots[j] if s not in usedB]; rng.shuffle(pool)
        for g in range(KA):
            if j not in Ah[g]: take(g, pool.pop())
    # ---- B-hubs: no condition
    Bh = [dict() for _ in range(KB)]
    for j in range(L):
        pool = list(Aslots[j]); rng.shuffle(pool)
        for h in range(KB): Bh[h][j] = pool[h]
    Bh = [[h[j] for j in range(L)] for h in Bh]; Ah = [[g[j] for j in range(L)] for g in Ah]
    # ---- the hub rule, checked on the final assignment (Proposition 7.2 hypothesis)
    ok = bad = 0
    for t in DH:
        for l, (m, z, om) in PT.items():
            g = [a for a in Ah if a[t[1]] == (t[1], l, t)]
            if len(g) == 1 and g[0][t[0]][1] in G.lines[m]: ok += 1
            else: bad += 1
    print('hub rule: %d instances satisfied, %d violated%s' % (ok, bad, ' (BREAK: pair %s)' % (broken,) if brk else ''))
    n0, E0 = build(G, types, M, R, Bh, Ah, [], arcs=arcs)
    nv = L * 2 * N
    D0 = hub_D0(n0, E0, list(range(nv, nv + KB + KA)))
    for sd in range(6):
        Y, cost = search(D0, KB, KA, q - r, seed=seed * 100 + sd, iters=int(os.environ.get('HUBITERS', '4000')))
        print('  hub graph seed', sd, 'same-colour hub pairs at distance > 4:', cost); sys.stdout.flush()
        if cost == 0: break
    assert cost == 0, 'no hub graph'
    n, E = build(G, types, M, R, Bh, Ah, Y, arcs=arcs)
    write_edges(out + '.edges', n, E)
    json.dump(dict(q=q, r=r, types=types, arcs=arcs, ovoid_Q4=O, T=T, K_B=KB, K_A=KA, Bhub_slots=Bh, Ahub_slots=Ah, Y=Y,
                   nonfriendly={'%d,%d' % t: dict(R=sorted(R[t]), M=M[t]) for t in arcs if types[t[0]] == types[t[1]]},
                   W_points=[list(p) for p in Wq.coords], W_lines=[list(l) for l in Wq.lines],
                   pairs_at_ovoid_points=len(zO) // 2, hub_rule=dict(ok=ok, violated=bad), seed=seed,
                   note='G = Q(4,q) = gqlib.W(q).dual(); friendly matchings = identity; slots (level, element, arc); '
                        'built by research/theorems/d5relax/build_zo.py'),
              open(out + '.json', 'w'), default=int)
    print('wrote %s.edges (n=%d, %d edges) and %s.json' % (out, n, len(E), out))


if __name__ == '__main__':
    main()
