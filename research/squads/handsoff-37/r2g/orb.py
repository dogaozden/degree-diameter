# r2g: exhaustive search over cubic bipartite graphs with a prescribed colour-preserving permutation group G.
# Sides are unions of G-orbits G/K (K any subgroup, stabilisers may be non-trivial). Edges are unions of edge orbits.
import sys, time, random, itertools
from collections import defaultdict

def pmul(a, b):          # apply a then b
    return tuple(b[x] for x in a)

def group_from_gens(gens):
    n = len(gens[0]); e = tuple(range(n))
    elems = [e]; idx = {e: 0}; fr = [e]
    while fr:
        new = []
        for x in fr:
            for g in gens:
                y = pmul(x, g)
                if y not in idx:
                    idx[y] = len(elems); elems.append(y); new.append(y)
        fr = new
    N = len(elems)
    gi = [idx[g] for g in gens]
    mult = [[idx[pmul(elems[i], elems[j])] for j in range(N)] for i in range(N)]
    inv = [0]*N
    for i in range(N):
        for j in range(N):
            if mult[i][j] == 0:
                inv[i] = j; break
    return dict(elems=elems, mult=mult, inv=inv, N=N, gens=gi)

def closure(G, gens_idx):
    mult = G['mult']; S = {0}; fr = [0]
    while fr:
        new = []
        for x in fr:
            for g in gens_idx:
                y = mult[x][g]
                if y not in S:
                    S.add(y); new.append(y)
        fr = new
    return frozenset(S)

def all_subgroups(G):
    N = G['N']
    cyc = {}
    for g in range(N):
        K = closure(G, [g])
        if K not in cyc: cyc[K] = [g]
    cycl = list(cyc.items())
    known = {frozenset([0]): []}
    work = [frozenset([0])]
    while work:
        H = work.pop()
        gH = known[H]
        for C, gC in cycl:
            if C <= H: continue
            J = closure(G, gH + gC)
            if J not in known:
                known[J] = gH + gC; work.append(J)
    return known   # subgroup (frozenset) -> generator indices

def conj_classes(G, subs):
    mult, inv = G['mult'], G['inv']
    seen = set(); classes = []
    for K in sorted(subs, key=lambda s: -len(s)):
        if K in seen: continue
        cl = set()
        for g in range(G['N']):
            gi = inv[g]
            cl.add(frozenset(mult[mult[gi][k]][g] for k in K))
        seen |= cl
        classes.append(K)
    return classes

def coset_action(G, K):
    """points = left cosets xK; returns (npts, reps, cid, act[g] list over generators+identity via full table)"""
    mult = G['mult']; N = G['N']
    cid = [-1]*N; reps = []
    for x in range(N):
        if cid[x] >= 0: continue
        p = len(reps); reps.append(x)
        for k in K:
            cid[mult[x][k]] = p
    npts = len(reps)
    gact = {}
    for g in G['gens']:
        gact[g] = [cid[mult[g][reps[p]]] for p in range(npts)]
    return npts, reps, gact

def edge_orbits(G, X, Y):
    """X, Y = (npts, gact). returns list of (pairs, dX, dY) for orbits of G on X x Y"""
    nx, gx = X; ny, gy = Y
    parent = list(range(nx*ny))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for g in G['gens']:
        for p in range(nx):
            for q in range(ny):
                a = find(p*ny+q); b = find(gx[g][p]*ny + gy[g][q])
                if a != b: parent[a] = b
    orb = defaultdict(list)
    for p in range(nx):
        for q in range(ny):
            orb[find(p*ny+q)].append((p, q))
    out = []
    for pairs in orb.values():
        dX = sum(1 for (p, q) in pairs if p == 0)
        dY = sum(1 for (p, q) in pairs if q == 0)
        out.append((pairs, dX, dY))
    return out

def far_count(n, adj, D=7):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    tot = 0
    for v in range(n):
        tot += n - bin(reach[v]).count('1')
    return tot // 2

def compositions(sizes, m, maxorb):
    """multisets (as lists of class ids) with sum of sizes == m and at most maxorb items"""
    res = []
    C = len(sizes)
    def rec(c, rem, cur):
        if len(cur) > maxorb: return
        if c == C:
            if rem == 0: res.append(list(cur))
            return
        s = sizes[c]
        k = 0
        while k*s <= rem and len(cur)+k <= maxorb:
            rec(c+1, rem-k*s, cur + [c]*k)
            k += 1
    rec(0, m, [])
    return res

RNG = None

class Setup:
    def __init__(self, G, classes):
        self.G = G; self.classes = classes
        self.K = classes
        self.sizes = [G['N']//len(K) for K in classes]
        self.cosets = [coset_action(G, K) for K in classes]
        self.eo_cache = {}
    def eo(self, ca, cb):
        key = (ca, cb)
        if key not in self.eo_cache:
            X = self.cosets[ca]; Y = self.cosets[cb]
            self.eo_cache[key] = edge_orbits(self.G, (X[0], X[2]), (Y[0], Y[2]))
        return self.eo_cache[key]

def solve_composition(S, sideA, sideB, cap, deadline, rng=None, collect=None):
    """sideA, sideB: lists of class ids (instances). Enumerate G-invariant cubic bipartite graphs.
    yields graphs as (n, adj). Returns (number of solutions seen, best far, best adj)."""
    nA, nB = len(sideA), len(sideB)
    offA = []; o = 0
    for c in sideA: offA.append(o); o += S.sizes[c]
    mA_tot = o
    offB = []; o2 = 0
    for c in sideB: offB.append(o2); o2 += S.sizes[c]
    mB_tot = o2
    if mA_tot != mB_tot: raise ValueError
    m = mA_tot
    edges = []   # dict: ends (nodeA, nodeB) pairs list with global ids; wA, wB
    inc = [[] for _ in range(nA+nB)]
    for i, ca in enumerate(sideA):
        for j, cb in enumerate(sideB):
            for pairs, dX, dY in S.eo(ca, cb):
                eid = len(edges)
                gp = [(offA[i]+p, m+offB[j]+q) for (p, q) in pairs]
                edges.append((i, nA+j, dX, dY, gp))
                inc[i].append(eid); inc[nA+j].append(eid)
    E = len(edges)
    status = [0]*E
    res = [3]*(nA+nB)
    w = lambda e, v: edges[e][2] if v < nA else edges[e][3]
    other = lambda e, v: edges[e][1] if edges[e][0] == v else edges[e][0]
    sols = [0]; best = [10**9, None]
    stats = {'nodes': 0, 'hit_cap': False}
    # feasibility of a node: its undecided candidate list
    def dfs():
        if sols[0] >= cap or time.time() > deadline:
            stats['hit_cap'] = True; return
        stats['nodes'] += 1
        bv = None; bc = None
        for v in range(nA+nB):
            if res[v] > 0:
                cand = [e for e in inc[v] if status[e] == 0 and w(e, v) <= res[v]
                        and w(e, other(e, v)) <= res[other(e, v)]]
                if not cand: return
                if bc is None or len(cand) < len(bc):
                    bv, bc = v, cand
                    if len(cand) == 1: break
        if bc is None:
            sols[0] += 1
            adj_edges = [e for e in range(E) if status[e] == 1]
            ev = []
            for e in adj_edges:
                ev.extend(edges[e][4])
            f = None
            n = 2*m
            adj = [[] for _ in range(n)]
            for (a, b) in ev:
                adj[a].append(b); adj[b].append(a)
            f = far_count(n, adj)
            if f < best[0]:
                best[0] = f; best[1] = ev
            if collect is not None and f <= collect[0]:
                collect[1].append((f, list(ev)))
            return
        if RNG is not None: RNG.shuffle(bc)
        for t, e in enumerate(bc):
            # include e, exclude bc[:t]
            for x in bc[:t]: status[x] = 2
            status[e] = 1
            ea, eb = edges[e][0], edges[e][1]
            res[ea] -= edges[e][2]; res[eb] -= edges[e][3]
            dfs()
            res[ea] += edges[e][2]; res[eb] += edges[e][3]
            status[e] = 0
            for x in bc[:t]: status[x] = 0
            if sols[0] >= cap or time.time() > deadline:
                stats['hit_cap'] = True; break
    # Node degrees: an instance with no incident edges cannot be cubic
    if any(len(inc[v]) == 0 for v in range(nA+nB)):
        return 0, None, None, stats
    dfs()
    return sols[0], best[0], best[1], stats, m

if __name__ == '__main__':
    pass
