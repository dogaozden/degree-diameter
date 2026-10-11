import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact small constructions (kept for calibration-style cases).
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
# New construction: vertex-transitive Haar graphs over finite groups.
#
# Vertices: A_g = g and B_h = n + h for g, h in G (|G| = n).
# Edges: A_g ~ B_{g*s} for s in S, |S| = d. This is d-regular and bipartite.
# Left multiplication is an automorphism, so the diameter is decided by two
# BFS runs, one from A_e and one from B_e. A local search over S minimises the
# number of unreached (source, vertex) pairs, using cheap numpy frontier steps.
# Groups are semidirect products Z_m x| Z_k (non-abelian preferred), with a
# cyclic fallback.
# ----------------------------------------------------------------------------

def _haar_graph_nonabelian_options(n):
    """Return (m, k, r) triples giving non-abelian groups Z_m x| Z_k of order n."""
    opts = []
    for k in range(2, n + 1):
        if n % k:
            continue
        m = n // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _mul_table(m, k, r):
    """Multiplication table Mul[g, s] = g*s for Z_m x| Z_k, element (a, b) coded a*k+b."""
    n = m * k
    x = np.arange(n, dtype=np.int64)
    a = x // k
    b = x % k
    P = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    Mul = ((a[:, None] + P[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return Mul


def _bfs_unreached(n, Rs, Qs, startA, D):
    """Count unreached (vertex) entries after D BFS steps from a fixed source on one side.

    Rs[i][g] = g*S_i gives A -> B moves. Qs[i][h] = h*S_i^{-1} gives B -> A moves.
    """
    visA = np.zeros(n, dtype=bool)
    visB = np.zeros(n, dtype=bool)
    fr = np.zeros(n, dtype=bool)
    if startA:
        visA[0] = True
        fr[0] = True
        onA = True
    else:
        visB[0] = True
        fr[0] = True
        onA = False
    for _ in range(D):
        idx = np.flatnonzero(fr)
        if idx.size == 0:
            break
        tabs = Rs if onA else Qs
        nxt = np.zeros(n, dtype=bool)
        nxt[tabs[:, idx].ravel()] = True
        if onA:
            new = nxt & ~visB
            visB |= new
        else:
            new = nxt & ~visA
            visA |= new
        fr = new
        onA = not onA
    return 2 * n - int(visA.sum()) - int(visB.sum())


def _cost(n, MT, inv, S, D):
    """Number of unreached (source, vertex) pairs over both source sides; 0 iff diameter <= D."""
    Rs = MT[S]
    Qs = MT[inv[S]]
    return _bfs_unreached(n, Rs, Qs, True, D) + _bfs_unreached(n, Rs, Qs, False, D)


def _climb(n, d, D, MT, inv, rng, deadline, iters, patience):
    """Local search over connection sets S of size d. Returns S (list) or None."""
    S = rng.sample(range(n), d)
    cost = _cost(n, MT, inv, S, D)
    stale = 0
    for _ in range(iters):
        if cost == 0 or stale > patience or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(n)
        if new in S:
            stale += 1
            continue
        old = S[i]
        S[i] = new
        c = _cost(n, MT, inv, S, D)
        if c <= cost:
            stale = 0 if c < cost else stale + 1
            cost = c
        else:
            S[i] = old
            stale += 1
    return list(S) if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

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

    if D == 2:
        return best

    # Exact constructions for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: Haar graphs over groups of order n (per side), with an
    # adaptive target that grows on success and shrinks on failure.
    lo = max(d, best_n // 2)
    step = max(1, lo // 16)
    opt_cache = {}

    while time.monotonic() < deadline:
        target = lo + step + rng.randrange(0, 3)
        target = min(target, 1600)
        if target <= lo:
            target = lo + 1
        if target > 1600:
            break

        if target not in opt_cache:
            opt_cache[target] = _haar_graph_nonabelian_options(target)
        opts = opt_cache[target]
        if opts and rng.random() < 0.9:
            m, k, r = rng.choice(opts)
        else:
            m, k, r = target, 1, 1  # cyclic fallback

        Mul = _mul_table(m, k, r)
        inv = np.argmax(Mul == 0, axis=1)
        MT = np.ascontiguousarray(Mul.T)  # MT[s, g] = g*s

        S = _climb(target, d, D, MT, inv, rng, deadline, 2000, 300)
        if S is None:
            step = max(1, step // 2)
            continue

        edges = []
        for s in S:
            row = MT[s]
            for g in range(target):
                edges.append((g, target + int(row[g])))
        before = best_n
        consider(2 * target, edges)
        if best_n > before:
            lo = best_n // 2
            step = max(1, min(step * 2, max(1, lo // 4)))
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
