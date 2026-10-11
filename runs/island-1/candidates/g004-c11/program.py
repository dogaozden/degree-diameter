import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# D = 3: Araujo-Pardo--Lopez base graphs plus a greedy pair-extension.
#
# Extension idea: add a new vertex u on side A and v on side B with edge uv.
# Let S be a set of B-vertices covering all of the old A-side in their
# neighbourhoods, and T a set of A-vertices covering all old B-side. Then
# u reaches every old A-vertex in 2 steps and every old B-vertex in 3 steps,
# and symmetrically for v. Old distances never grow. Each use consumes one
# spare degree on S and T. Candidates are checked with lib.is_valid, so an
# invalid attempt is simply discarded.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _sides(n, adj):
    """Two-colour a bipartite graph (sides 0/1). Unreached vertices default to 0."""
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return [x if x != -1 else 0 for x in side]


def _cover(cands, need, adj, d, budget, rng):
    """Greedy set cover: choose <= budget candidates with spare degree whose neighbourhoods cover need."""
    uncovered = set(need)
    pool = [c for c in cands if len(adj[c]) < d]
    rng.shuffle(pool)
    chosen = []
    while uncovered:
        if len(chosen) >= budget:
            return None
        best, best_gain = None, 0
        for c in pool:
            g = len(adj[c] & uncovered)
            if g > best_gain:
                best, best_gain = c, g
        if best is None:
            return None
        chosen.append(best)
        pool.remove(best)
        uncovered -= adj[best]
    return chosen


def _extend(n, edges, d, D, rng, deadline):
    """Repeatedly add a new A-B vertex pair while the result stays valid. Requires D == 3."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 40:
        adj = _adjacency(n, edges)
        side = _sides(n, adj)
        A = [x for x in range(n) if side[x] == 0]
        B = [x for x in range(n) if side[x] == 1]
        S = _cover(B, A, adj, d, d - 1, rng)
        T = _cover(A, B, adj, d, d - 1, rng)
        if S is None or T is None:
            fails += 1
            continue
        u, v = n, n + 1
        new_edges = edges + [(u, s) for s in S] + [(v, t) for t in T] + [(u, v)]
        if lib.is_valid(n + 2, new_edges, d, D):
            n, edges = n + 2, new_edges
            fails = 0
        else:
            fails += 1
    return n, edges


def _d3_bases(d):
    """Strong D = 3 bases: PG(2,q) with q+1 <= d, and the Araujo-Pardo--Lopez graph with q+2 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            break
    for q in range(d - 2, 2, -1):
        if lib.is_prime_power(q):
            try:
                out.append(lib.araujo_lopez_graph(q))
            except Exception:
                pass
            break
    return out


# ----------------------------------------------------------------------------
# Group voltage lifts over semidirect products.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
#
# Left multiplication by any h is an automorphism, so each class A_i and B_j is
# one orbit. Hence the graph has diameter <= D iff, for each of the 2k base
# representatives, a BFS of depth D reaches every vertex.
#
# Search: simulated-annealing-style hill climb over voltages, with iterated
# restarts. Each restart either samples a fresh group and random voltages, or
# (once a near-valid configuration has been found) perturbs the best such
# "elite" configuration by a few voltage changes. Perturbing a near miss is
# usually more productive than starting from scratch, since most of the
# structure is already right.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _perms(mul, G, darts):
    return [_right_perm(mul, G, s) for _, _, s in darts]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _anneal(d, D, k, G, mul, darts, iters, deadline):
    """Hill-climb over voltages from the given darts. Returns (cost, darts, perms)."""
    perms = _perms(mul, G, darts)
    cost = _cost(k, G, D, darts, perms)
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = _ANNEAL_RNG.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = _ANNEAL_RNG.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or _ANNEAL_RNG.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm
    return cost, darts, perms


_ANNEAL_RNG = random.Random(0)


def build(d, D, seed, time_limit):
    global _ANNEAL_RNG
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)
    _ANNEAL_RNG = rng

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        bases = _d3_bases(d)
        for bn, be in bases:
            consider(bn, be)
        ext_end = start + 0.4 * time_limit
        for idx, (bn, be) in enumerate(bases):
            now = time.monotonic()
            share = max(0.0, ext_end - now) / (len(bases) - idx)
            n2, e2 = _extend(bn, be, d, D, rng, now + share)
            consider(n2, e2)
    else:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

    # Main search: group voltage lifts with 1-3 base vertices per side.
    # elite = (cost, k, G, mul, darts) for the closest-to-valid configuration so far.
    elite = None
    while time.monotonic() < deadline:
        if elite is not None and rng.random() < 0.5:
            _, k, G, mul, base_darts = elite
            darts = [list(x) for x in base_darts]
            for _ in range(3):
                idx = rng.randrange(len(darts))
                darts[idx][2] = rng.randrange(G)
        else:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            G, mul = g
            darts = _random_darts(d, k, G, rng)

        cost, darts, perms = _anneal(d, D, k, G, mul, darts, 600, deadline)
        if cost == 0:
            n2, e2 = _edges(k, G, darts, perms)
            consider(n2, e2)
        elif cost < _BIG and (elite is None or cost < elite[0]):
            elite = (cost, k, G, mul, [list(x) for x in darts])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
