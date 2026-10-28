"""Mixed-hub construction (card c17). Levels = incidence graph of W(q) (points 0..np-1, lines np..), typed H/D on a
regular tournament of 2r+1 levels. Friendly arcs: identity matching; freed sets: partial ovoid of points (H->D) and a
regular spread of lines (D->H). Same-type arcs: arbitrary bijection, nothing freed. Hubs: K vertices, each adjacent to
exactly one slot per level (a freed element; A-slots are freed out-elements, B-slots freed in-elements, either side),
plus Y-edges: hubs with the same pattern (A/B per level) form cliques of size <= q-r+1.
usage: python3 mixed.py q r ARCS TYPES Kcap b_seed out.edges"""
import sys, random, itertools, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, regular_spread_W
from tourn import arcs_random

def greedy_partial_ovoid(G, rng, tries=200):
    best = []
    for _ in range(tries):
        order = list(range(G.np)); rng.shuffle(order)
        S = []
        for p in order:
            if all(not G.col[p, s] for s in S):
                S.append(p)
        if len(S) > len(best): best = S
    return sorted(best)

def build(q, r, arcs, types, K, rng, b_tries=200):
    G = W(q); n = 2 * r + 1; NP, NL = G.np, G.nl; per = NP + NL
    spread = regular_spread_W(G)
    pov = greedy_partial_ovoid(G, rng, b_tries)
    def Ael(j, i):  return i if types[j] == 'H' else NP + i     # A-element of level j with local index i
    def Bel(j, x):  return NP + x if types[j] == 'H' else x      # B-element of level j with local index x
    edges = []
    for j in range(n):
        for l, pts in enumerate(G.lines):
            for p in pts:
                edges.append((j * per + p, j * per + NP + l))
    freed = {}; M = {}
    for (u, v) in arcs:
        if types[u] == 'H' and types[v] == 'D':
            R = pov; M[(u, v)] = list(range(NP))
        elif types[u] == 'D' and types[v] == 'H':
            R = spread; M[(u, v)] = list(range(NL))
        else:
            R = []; M[(u, v)] = [ (i * 7 + 3) % NP for i in range(NP)]   # arbitrary bijection (same type)
        Rs = set(R); freed[(u, v)] = Rs
        for i in range(NP):
            if i in Rs: continue
            edges.append((u * per + Ael(u, i), v * per + Bel(v, M[(u, v)][i])))
    # slots per level
    Aslots = {j: [] for j in range(n)}; Bslots = {j: [] for j in range(n)}
    for (u, v) in arcs:
        for i in freed[(u, v)]:
            Aslots[u].append(Ael(u, i))
            Bslots[v].append(Bel(v, M[(u, v)][i]))
    tot = {j: len(Aslots[j]) + len(Bslots[j]) for j in range(n)}
    K = min(K, min(tot.values()))
    # pattern columns: NA[j] hubs take an A-slot at level j (within capacity), the rest a B-slot
    NA = {}
    for j in range(n):
        lo = max(0, K - len(Bslots[j])); hi = min(K, len(Aslots[j]))
        NA[j] = (lo + hi) // 2
    for attempt in range(5000):
        cols = {}
        for j in range(n):
            perm = list(range(K)); rng.shuffle(perm)
            cols[j] = set(perm[:NA[j]])
        pat = [tuple(1 if h in cols[j] else 0 for j in range(n)) for h in range(K)]
        cls = {}
        for h, p in enumerate(pat): cls.setdefault(p, []).append(h)
        if max(len(c) for c in cls.values()) <= q - r + 1:
            break
    else:
        raise SystemExit('no pattern assignment with classes <= q-r+1')
    slotA = {j: iter(rng.sample(Aslots[j], len(Aslots[j]))) for j in range(n)}
    slotB = {j: iter(rng.sample(Bslots[j], len(Bslots[j]))) for j in range(n)}
    nv = n * per
    hubs = []
    for h in range(K):
        s = []
        for j in range(n):
            s.append(next(slotA[j]) if pat[h][j] else next(slotB[j]))
        hubs.append(s)
        for j in range(n):
            edges.append((nv + h, j * per + s[j]))
    # Y: cliques inside each pattern class
    yd = {}
    for p, cl in cls.items():
        for a, b in itertools.combinations(cl, 2):
            edges.append((nv + a, nv + b)); yd[a] = yd.get(a, 0) + 1; yd[b] = yd.get(b, 0) + 1
    N = nv + K
    deg = [0] * N
    for a, b in edges: deg[a] += 1; deg[b] += 1
    info = dict(K=K, tot=tot, NA=NA, classes=len(cls), maxclass=max(len(c) for c in cls.values()),
                maxdeg=max(deg), pov=len(pov), spread=len(spread), arcs=arcs, types=''.join(types))
    return N, edges, info

if __name__ == '__main__':
    q, r = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(int(sys.argv[3]))
    arcs = json.loads(sys.argv[4]); types = sys.argv[5]; K = int(sys.argv[6]); out = sys.argv[7]
    N, E, info = build(q, r, [tuple(a) for a in arcs], types, K, rng)
    with open(out, 'w') as f:
        f.write('%d\n' % N)
        for a, b in E: f.write('%d %d\n' % (a, b))
    print(json.dumps(info))
