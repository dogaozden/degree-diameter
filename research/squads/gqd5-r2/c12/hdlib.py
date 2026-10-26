"""c12 helper: typed 7-level graph with arbitrary freed sets on H->D arcs (identity matching), D->H arcs, optional
hub permutations.  Only the level graph plus hubs with an optional hub graph Y is built; validity is checked by
all-pairs BFS in python (small q) or by the C apsp binary."""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, regular_spread_W, is_partial_ovoid, is_partial_spread
from levels import build, rotational_arcs

def setup(q):
    Wq = W(q); G = Wq.dual('Q(4,%d)' % q)
    ovoid = regular_spread_W(Wq)
    return Wq, G, ovoid

def greedy_partial_spread(G, seed=0, tries=200):
    """partial spread of Q(4,q) (= partial ovoid of W(q)), random greedy on line ids of G"""
    rng = random.Random(seed); best = []
    for _ in range(tries):
        order = list(range(G.nl)); rng.shuffle(order); S = []
        bad = np.zeros(G.nl, dtype=bool)
        for l in order:
            if not bad[l]:
                S.append(l); bad |= G.con[l]; bad[l] = True
        if len(S) > len(best): best = S
    return sorted(best)

def make(q, types, arcs, RHD, RDH, Y=(), perms=None):
    """RHD: freed point set used on every H->D arc; RDH: freed line set on every D->H arc (identity matchings).
    perms: optional dict level -> list of slot orders (hub h uses slot perm[h]).  Returns (n, edges, KB, KA, Bhubs, Ahubs)."""
    Wq, G, _ = setup(q)
    N = G.np
    L = len(types)
    M = {}; R = {}
    for (u, v) in arcs:
        M[(u, v)] = list(range(N))
        if types[u] == 'H' and types[v] == 'D':
            R[(u, v)] = set(RHD)
        elif types[u] == 'D' and types[v] == 'H':
            R[(u, v)] = set(RDH)
        else:
            R[(u, v)] = set()
    Aslots = {j: [] for j in range(L)}; Bslots = {j: [] for j in range(L)}
    for (u, v) in arcs:
        for a in sorted(R[(u, v)]):
            Aslots[u].append((u, a, (u, v)))
            Bslots[v].append((v, M[(u, v)][a], (u, v)))
    KB = min(len(Aslots[j]) for j in range(L)); KA = min(len(Bslots[j]) for j in range(L))
    Bhubs = [[Aslots[j][h] for j in range(L)] for h in range(KB)]
    Ahubs = [[Bslots[j][g] for j in range(L)] for g in range(KA)]
    n, E = build(G, types, M, R, Bhubs, Ahubs, list(Y), arcs=arcs)
    return n, E, KB, KA

def bad_pairs(n, E, D=5, maxdeg=None):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b); adj[b].append(a)
    deg_bad = 0 if maxdeg is None else sum(1 for x in adj if len(x) > maxdeg)
    bad = 0
    for s in range(n):
        dist = [-1] * n; dist[s] = 0; fr = [s]; d = 0
        while fr and d < D:
            d += 1; nf = []
            for x in fr:
                for y in adj[x]:
                    if dist[y] < 0:
                        dist[y] = d; nf.append(y)
            fr = nf
        bad += sum(1 for t in range(s + 1, n) if dist[t] < 0)
    return bad, deg_bad
