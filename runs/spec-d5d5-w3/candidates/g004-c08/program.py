import itertools
import math
import random
import time

import lib

ITERS0 = 300          # initial annealing steps per semidirect (order, group) try
MAX_GROUPS = 12       # semidirect groups tried per order N
BAND = 6              # orders swept above the current lower bound (phase B)
PERM_LO = 168         # smallest group order worth searching in phase A
_TABLE_CACHE = {}
_PERM_CACHE = None


# ----------------------------------------------------------------------------
# Structured baselines: projective planes and generalized quadrangles.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Permutation-group bi-Cayley lifts (phase A).
# Base: A_x ~ B_{x s} for s in S, |S| = d, 1 in S WLOG. Left multiplication
# acts transitively on A and on B, so diameter <= D iff the two BFS from
# A_e and B_e reach everything within D.
# ----------------------------------------------------------------------------

def _cyc(n, cycles):
    """Permutation of range(n) given by disjoint cycles, as a tuple."""
    p = list(range(n))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)


def _closure(gens, npts, cap):
    """All elements of the permutation group generated by gens, or None if more than cap."""
    ident = tuple(range(npts))
    seen = {ident: 0}
    elems = [ident]
    frontier = [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(p[i] for i in g)
                if q not in seen:
                    if len(elems) >= cap:
                        return None
                    seen[q] = len(elems)
                    elems.append(q)
                    nxt.append(q)
        frontier = nxt
    return elems


class _PermGroup:
    """A finite permutation group with lazily cached right-multiplication columns."""

    def __init__(self, elems):
        self.elems = elems
        self.G = len(elems)
        self.idx = {p: i for i, p in enumerate(elems)}
        self.inv = [0] * self.G
        for i, p in enumerate(elems):
            q = [0] * len(p)
            for k, v in enumerate(p):
                q[v] = k
            self.inv[i] = self.idx[tuple(q)]
        self.cols = {}

    def col(self, g):
        """col[x] = index of x*g (composition x after g)."""
        c = self.cols.get(g)
        if c is None:
            pg = self.elems[g]
            idx = self.idx
            c = [idx[tuple(P[j] for j in pg)] for P in self.elems]
            self.cols[g] = c
        return c


def _embed(g, off, total):
    p = list(range(total))
    for i, v in enumerate(g):
        p[off + i] = off + v
    return tuple(p)


def _product(factors):
    """Direct product of permutation factors (n, gens) acting on disjoint supports."""
    total = sum(n for n, _ in factors)
    gens = []
    off = 0
    for n, gs in factors:
        for g in gs:
            gens.append(_embed(g, off, total))
        off += n
    return total, gens


def _mob_factor(pgl):
    """PSL(2,7) (or PGL(2,7)) acting on the projective line; 7 = infinity."""
    p = 7
    INF = 7

    def tr(x):
        return INF if x == INF else (x + 1) % p

    def mu(a):
        return lambda x: INF if x == INF else (a * x) % p

    def iv(x):
        if x == INF:
            return 0
        if x == 0:
            return INF
        return (-pow(x, -1, p)) % p

    def perm(f):
        return tuple(f(x) for x in range(8))

    gens = [perm(tr), perm(mu(3 if pgl else 2)), perm(iv)]
    return (8, gens)


def _gl23_factor():
    """GL(2,3) acting on the 8 nonzero vectors of GF(3)^2."""
    vecs = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
    vi = {v: i for i, v in enumerate(vecs)}

    def mat(M):
        (m00, m01), (m10, m11) = M
        return tuple(vi[((m00 * v[0] + m01 * v[1]) % 3, (m10 * v[0] + m11 * v[1]) % 3)]
                     for v in vecs)

    gens = [mat(((1, 1), (0, 1))), mat(((0, 1), (2, 0))), mat(((2, 0), (0, 1)))]
    return (8, gens)


def _agl_p(p, g):
    """AGL(1,p) acting on p points."""
    return (p, [tuple((x + 1) % p for x in range(p)),
                tuple((g * x) % p for x in range(p))])


def _agl_gf16():
    """AGL(1,16) acting on GF(16)."""
    F = lib.GF(16)
    gens = [tuple(F.add(x, b) for x in range(16)) for b in (1, 2, 4, 8)]
    g = F.primitive_element()
    gens.append(tuple(F.mul(g, x) for x in range(16)))
    return (16, gens)


def _perm_candidates():
    """Permutation groups of order at most 400, sorted by order (cached)."""
    global _PERM_CACHE
    if _PERM_CACHE is not None:
        return _PERM_CACHE
    S3 = (3, [_cyc(3, [(0, 1)]), _cyc(3, [(0, 1, 2)])])
    S4 = (4, [_cyc(4, [(0, 1)]), _cyc(4, [(0, 1, 2, 3)])])
    A4 = (4, [_cyc(4, [(0, 1, 2)]), _cyc(4, [(0, 1), (2, 3)])])
    A5 = (5, [_cyc(5, [(0, 1, 2)]), _cyc(5, [(2, 3, 4)])])
    S5 = (5, [_cyc(5, [(0, 1)]), _cyc(5, [(0, 1, 2, 3, 4)])])
    PSL = _mob_factor(False)
    PGL = _mob_factor(True)
    GL = _gl23_factor()
    AGL17 = _agl_p(17, 3)
    AGL16 = _agl_gf16()

    def Z(k):
        return (k, [_cyc(k, [tuple(range(k))])])

    combos = [[PSL], [PGL], [GL], [AGL17], [AGL16], [S5], [A5], [S4], [A4], [S3]]
    combos += [[S4, Z(k)] for k in range(2, 15)]
    combos += [[A4, Z(k)] for k in range(2, 29)]
    combos += [[A5, Z(k)] for k in range(2, 6)]
    combos += [[S5, Z(2)], [PSL, Z(2)], [S4, A4], [A4, A4, Z(2)],
               [S3, S4, Z(2)], [S4, S3], [A5, S3]]
    combos += [[GL, Z(k)] for k in range(2, 8)]

    out = []
    for factors in combos:
        total, gens = _product(factors)
        el = _closure(gens, total, 400)
        if el is None or len(el) < 3:
            continue
        out.append(_PermGroup(el))
    out.sort(key=lambda g: g.G)
    _PERM_CACHE = out
    return out


def _unreached_pg(grp, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_e and B_e."""
    G = grp.G
    N2 = 2 * G
    cols = [grp.col(s) for s in S]
    icols = [grp.col(grp.inv[s]) for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(N2)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for c in cols:
                        v = G + c[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - G
                    for c in icols:
                        v = c[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - count
    return total


def _anneal_pg(grp, d, D, rng, iters, deadline):
    """Simulated annealing over S = {1, s_1, ..., s_{d-1}} to zero unreached pairs."""
    G = grp.G
    if G - 1 < d - 1 or d < 2:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    cur = _unreached_pg(grp, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.1, 3.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, G)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached_pg(grp, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _edges_pg(grp, S):
    """Edge list of the bi-Cayley graph: A_x = x, B_y = G + y, A_x ~ B_{x s}."""
    G = grp.G
    E = []
    for s in S:
        c = grp.col(s)
        for x in range(G):
            E.append((x, G + c[x]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Semidirect-product bi-Cayley lifts (phase B, from the parent program).
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal_S(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, iters, deadline):
    """Try semidirect groups of order N until a connection set with diameter <= D is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, _, T, invs = _tables(m, k, r)
        S = _anneal_S(N, T, invs, d, D, rng, iters, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: bipartite, degree d, diameter 2. Safe fallback for every D >= 2.
    best = list(lib.haar_graph(d, range(d)))
    best_n = best[0]
    if D == 2:
        return best[0], best[1]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = [n, e]
            best_n = n
            return True
        return False

    moore = lib._moore_bound(d, D)

    if D == 3:
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best[0], best[1]
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if best_n < moore:
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.05 * budget, rng)
                consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if best_n < moore:
                n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.05 * budget, rng)
                consider(n2, e2)

    Nmax = moore // 2

    # Phase A: bi-Cayley lifts over non-metabelian permutation groups.
    if d >= 3 and best_n < moore:
        phase_end = start + 0.6 * budget
        iters = 100
        while time.monotonic() < phase_end and best_n < moore:
            lo_g = max(PERM_LO, best_n // 2 + 1)
            pool = [g for g in _perm_candidates() if lo_g <= g.G <= Nmax]
            if not pool:
                break
            for grp in pool:
                if time.monotonic() >= phase_end:
                    break
                if 2 * grp.G <= best_n:
                    continue
                S = _anneal_pg(grp, d, D, rng, iters, phase_end)
                if S is not None:
                    consider(*_edges_pg(grp, S))
            iters = min(iters * 2, 20000)

    # Phase B: semidirect bi-Cayley sweep over orders just above the current best.
    iters = ITERS0
    while time.monotonic() < deadline and best_n < moore and d >= 3:
        lo = best_n // 2 + 1
        if lo > Nmax:
            break
        before = best_n
        for N in range(lo, min(Nmax, lo + BAND) + 1):
            if time.monotonic() >= deadline:
                break
            if N <= d:
                continue
            res = _attempt(N, d, D, rng, iters, deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                if consider(2 * N, edges):
                    break
        if best_n == before:
            iters = min(iters * 2, 5000)

    if not lib.is_valid(best[0], best[1], d, D):
        best = list(lib.haar_graph(d, range(d)))
    return best[0], best[1]
