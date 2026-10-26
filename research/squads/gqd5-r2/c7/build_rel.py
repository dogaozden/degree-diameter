"""Card r2c7: HHDHD over Q(4,5), rotational tournament j -> j+1, j+2 (q=5, r=2, 5 levels).
Relaxed set T of lines of Q(4,5) on the D->H arcs (2->3, 4->0, 4->1); ovoid O on the H->D arcs (0->2, 1->2, 3->4);
non-friendly arcs (0->1, 1->3, 3->0, 2->4) are index bijections freeing nothing.
Hub slots are chosen by a SAT model (python-sat); with --rule the RELAXED-PAIR RULE is imposed as clauses.
usage: build_rel.py T_FILE OUT_PREFIX RULE(0|1) K(0 = max) SEED"""
import sys, json, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, regular_spread_W, is_partial_ovoid
from levels import build, write_edges, apsp
from hubopt import hub_D0, search, bad_pairs
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

q, r = 5, 2
types = 'HHDHD'
arcs = [(j, (j + k) % 5) for j in range(5) for k in (1, 2)]
HD = [(0, 2), (1, 2), (3, 4)]          # H->D arcs, free the ovoid
DH = [(2, 3), (4, 0), (4, 1)]          # D->H arcs, free T
NF = [(0, 1), (1, 3), (3, 0), (2, 4)]  # non-friendly, free nothing

Wq = W(q); G = Wq.dual('Q(4,5)')
N = G.np
O = sorted(regular_spread_W(Wq))
assert is_partial_ovoid(G, O) and len(O) == q * q + 1
Oset = set(O)

def load_T(path):
    lines = open(path).read().split()
    k = int(lines[0]); return sorted(int(x) for x in lines[1:1 + k])

def pt_on(m):                      # the unique ovoid point on line m of G
    pts = [p for p in G.lines[m] if p in Oset]; assert len(pts) == 1; return pts[0]

def analyse_T(T):
    partner = {}
    for l in T:
        ms = [m for m in T if m != l and G.con[l, m]]
        assert len(ms) <= 1, ('line meets two others', l, ms)
        if ms:
            m = ms[0]
            z = set(G.lines[l]) & set(G.lines[m]); assert len(z) == 1
            assert list(z)[0] not in Oset, 'concurrency point on ovoid'
            partner[l] = m
    return partner

def main():
    Tfile, out, rule, K, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    T = load_T(Tfile); partner = analyse_T(T)
    print('|T| =', len(T), 'paired lines =', len(partner), 'pairs =', len(partner) // 2, flush=True)
    M = {a: list(range(N)) for a in arcs}           # identity everywhere (non-friendly: index bijection)
    R = {}
    import os
    for a in arcs:
        R[a] = set(O) if a in HD else (set(T) if a in DH else set())
        if a in NF and os.environ.get('LD', '0') == '1':
            # two-point local duality on a non-friendly arc (Proposition 6.4): H->H on G, D->D on W(q) = G^D
            from localdual import local_duality_pair, pick_pair
            u = a[0]
            Hq = G if types[u] == 'H' else Wq
            avoid = O if types[u] == 'H' else T
            x, y, l, m = pick_pair(Hq, avoid_pts=avoid)
            M[a] = local_duality_pair(Hq, x, y, l, m)
            R[a] = {x, y}
    # slot universes: B-hub slots (A-elements of level j) and A-hub slots (B-elements of level j)
    UB = {j: [] for j in range(5)}; UA = {j: [] for j in range(5)}
    for a in arcs:
        u, v = a
        for x in sorted(R[a]):
            UB[u].append((u, x, a))
            UA[v].append((v, M[a][x], a))
    alpha = {j: len(UB[j]) for j in range(5)}; beta = {j: len(UA[j]) for j in range(5)}
    KB = min(alpha.values()); KA = min(beta.values())
    if K: KB, KA = min(KB, K), min(KA, K)
    print('alpha', alpha, 'beta', beta, 'K_B', KB, 'K_A', KA, flush=True)
    pool = IDPool()
    def xb(h, s): return pool.id(('B', h, s))
    def xa(g, s): return pool.id(('A', g, s))
    cls = []
    for tag, U, K_, var in (('B', UB, KB, xb), ('A', UA, KA, xa)):
        for h in range(K_):
            for j in range(5):
                lits = [var(h, s) for s in U[j]]
                cls.append(lits)
                enc = CardEnc.atmost(lits, 1, vpool=pool, encoding=EncType.seqcounter)
                cls.extend(enc.clauses)
        for j in range(5):
            for s in U[j]:
                lits = [var(h, s) for h in range(K_)]
                if len(lits) > 1:
                    cls.extend(CardEnc.atmost(lits, 1, vpool=pool, encoding=EncType.seqcounter).clauses)
    if rule:
        for h in range(KB):
            for s in UB[2]:                              # slot (2, l, 2->3), l paired with m -> level 3 slot O∩m
                l = s[1]
                if l in partner:
                    cls.append([-xb(h, s), xb(h, (3, pt_on(partner[l]), (3, 4)))])
            for s in UB[4]:                              # slot (4, l, 4->0) -> level 0 slot O∩m ; (4,l,4->1) -> level 1
                l = s[1]
                if l in partner:
                    tgt = (0, pt_on(partner[l]), (0, 2)) if s[2] == (4, 0) else (1, pt_on(partner[l]), (1, 2))
                    cls.append([-xb(h, s), xb(h, tgt)])
        for g in range(KA):
            for s in UA[0] + UA[1] + UA[3]:             # A-slot l (arrives from D-level 4 or 2) with partner m
                l = s[1]
                if l not in partner: continue
                m = partner[l]
                if s[2] in ((4, 0), (4, 1)):
                    cls.append([-xa(g, s), xa(g, (4, pt_on(m), (3, 4)))])
                else:                                     # (3, l, (2,3)) -> level 2 B-slot O∩m (either in-arc)
                    cls.append([-xa(g, s), xa(g, (2, pt_on(m), (0, 2))), xa(g, (2, pt_on(m), (1, 2)))])
    solver = Cadical153(bootstrap_with=cls)
    ok = solver.solve()
    print('SAT', ok, flush=True)
    if not ok: return
    model = set(l for l in solver.get_model() if l > 0)
    Bhubs = []
    for h in range(KB):
        Bhubs.append([next(s for s in UB[j] if xb(h, s) in model) for j in range(5)])
    Ahubs = []
    for g in range(KA):
        Ahubs.append([next(s for s in UA[j] if xa(g, s) in model) for j in range(5)])
    # slots as (level, element, arc): build() wants (j, a, t) with t = arc key
    Bh = [[(s[0], s[1], s[2]) for s in hub] for hub in Bhubs]
    Ah = [[(s[0], s[1], s[2]) for s in hub] for hub in Ahubs]
    n0, E0 = build(G, types, M, R, Bh, Ah, [], arcs=arcs)
    nv = 5 * 2 * N; hubs = list(range(nv, nv + KB + KA))
    D0 = hub_D0(n0, E0, hubs)
    Y, cost = None, None
    for sd in range(8):
        Y, cost = search(D0, KB, KA, q - r, seed=sd + seed * 100, iters=20000)
        print('hub search seed', sd, 'bad', cost, flush=True)
        if cost == 0: break
    n, E = build(G, types, M, R, Bh, Ah, Y, arcs=arcs)
    write_edges(out + '.edges', n, E)
    json.dump(dict(T=T, O=O, K_B=KB, K_A=KA, rule=rule, Bhubs=Bh, Ahubs=Ah, Y=Y, n=n, hub_bad=cost),
              open(out + '.json', 'w'))
    print('n =', n, 'hub-bad =', cost, flush=True)
    print('D=5:', apsp(out + '.edges', q + 1 + r, 5), flush=True)
    print('D=6:', apsp(out + '.edges', q + 1 + r, 6), flush=True)

if __name__ == '__main__':
    main()
