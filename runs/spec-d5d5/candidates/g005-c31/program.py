import itertools
import math
import random
import time

import numpy as np

import lib

# Search knobs.
MAX_GROUPS = 8        # groups tried per order N within one attempt
ITERS = 6000          # annealing steps per (group, order) try
WINDOW = 12           # candidate orders tried per sweep


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley lifts ("a-orbit" generalisation of the single-orbit
# bi-Cayley search).
#
# Group G = Z_m x|_r Z_k of order N. Vertices A_{i,x} and B_{j,y}, for
# i, j in range(a) and x, y in G, so there are 2*a*N vertices in total.
# A dart (i, j, g) adds the edges A_{i,x} -- B_{j, x g} for every x in G.
# Left multiplication by G is an automorphism, so the eccentricities only
# need to be read from the 2a representatives A_{i,e} and B_{j,e}.
#
# Every A orbit emits exactly d darts and every B orbit receives exactly d
# darts, so the graph is d-regular and bipartite. A state is a list of
# a*d darts (i, j, g). Moves change a dart's g, or swap the target orbits
# of two darts, so the source and target counts stay fixed. The cost is the
# number of (representative, vertex) pairs at distance more than D, computed
# by a vectorised multi-source BFS in numpy.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _init_darts(N, a, d, rng):
    """Random dart list: each source orbit gets d darts and each target orbit receives d."""
    srcs = [i for i in range(a) for _ in range(d)]
    tgts = [j for j in range(a) for _ in range(d)]
    rng.shuffle(tgts)
    darts, used = [], set()
    for i, j in zip(srcs, tgts):
        while True:
            g = rng.randrange(N)
            if (i, j, g) not in used:
                break
        used.add((i, j, g))
        darts.append((i, j, g))
    return darts


def _neighbours(N, a, d, darts, Tcol, invn):
    """Regular neighbour table of shape (2aN, d)."""
    V = 2 * a * N
    base_b = a * N
    nbr = np.empty((V, d), dtype=np.int64)
    fa = [0] * a
    fb = [0] * a
    for i, j, g in darts:
        s = fa[i]
        fa[i] += 1
        nbr[i * N:(i + 1) * N, s] = base_b + j * N + Tcol[g]
        t = fb[j]
        fb[j] += 1
        nbr[base_b + j * N: base_b + (j + 1) * N, t] = i * N + Tcol[invn[g]]
    return nbr


def _cost(N, a, d, D, darts, Tcol, invn):
    """Count (representative, vertex) pairs at distance more than D."""
    nbr = _neighbours(N, a, d, darts, Tcol, invn)
    V = 2 * a * N
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    total = 0
    for s in sources:
        seen = np.zeros(V, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            cand = nbr[front].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            seen[cand] = True
            cnt += cand.size
            front = cand
        total += V - cnt
    return int(total)


def _anneal(N, a, d, D, Tcol, invn, rng, iters, deadline):
    """Simulated annealing over dart lists to reach zero unreached pairs."""
    darts = _init_darts(N, a, d, rng)
    cur = _cost(N, a, d, D, darts, Tcol, invn)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.15, 1.5 * (1.0 - it / iters))
        k = rng.randrange(len(darts))
        new = list(darts)
        if a == 1 or rng.random() < 0.5:
            i, j, _ = darts[k]
            new[k] = (i, j, rng.randrange(N))
        else:
            k2 = rng.randrange(len(darts))
            i1, j1, g1 = darts[k]
            i2, j2, g2 = darts[k2]
            if j1 == j2:
                continue
            new[k] = (i1, j2, g1)
            new[k2] = (i2, j1, g2)
        if len(set(new)) < len(new):
            continue
        v = _cost(N, a, d, D, new, Tcol, invn)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(N, a, d, D, rng, deadline):
    """Try groups of order N until one yields a dart list with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        Tcol = [np.array([mul(x, g) for x in range(N)], dtype=np.int64) for g in range(N)]
        invn = [inv(g) for g in range(N)]
        darts = _anneal(N, a, d, D, Tcol, invn, rng, ITERS, deadline)
        if darts is not None:
            return darts, Tcol
    return None


def _edges(N, a, darts, Tcol):
    """Expand a dart list into the explicit graph (n, edges)."""
    edges = []
    base_b = a * N
    for i, j, g in darts:
        col = Tcol[g].tolist()
        for x in range(N):
            edges.append((i * N + x, base_b + j * N + col[x]))
    return 2 * a * N, edges


def _search(a, d, D, rng, dl, cur_n, consider, ascending):
    """Search for a valid a-orbit lift beating cur_n.

    Returns 'ok' on success, 'timeout' at the deadline, or 'exhausted' if no
    order above cur_n can fit under the Moore bound.
    """
    Nmax = lib._moore_bound(d, D) // (2 * a)
    lo = max(d + 1, cur_n // (2 * a) + 1)
    if lo > Nmax:
        return 'exhausted'
    if ascending:
        cands = list(range(lo, min(Nmax, lo + WINDOW) + 1))
    else:
        top = min(Nmax, Nmax // 2 + 3)
        cands = list(range(top, max(lo, top - WINDOW + 1) - 1, -1))
    if not cands:
        return 'exhausted'
    budget = 0.5
    while True:
        for N in cands:
            now = time.monotonic()
            if now >= dl:
                return 'timeout'
            res = _attempt(N, a, d, D, rng, min(dl, now + budget))
            if res is None:
                continue
            darts, Tcol = res
            n, edges = _edges(N, a, darts, Tcol)
            consider(n, edges)
            return 'ok'
        if time.monotonic() >= dl:
            return 'timeout'
        budget *= 2


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = max(0.5, 0.78 * time_limit - 1.0)
    deadline = t0 + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    # Calibration case: incidence graph of PG(2, d-1) meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best[0], best[1]

    # Phase 1: single-orbit bi-Cayley (a = 1), descending from the top window.
    p1 = t0 + 0.4 * total
    while time.monotonic() < p1:
        st = _search(1, d, D, rng, p1, best[0], consider, False)
        if st != 'ok':
            break

    # Phase 2: multi-orbit lifts (a = 2, 3) in alternating time slices.
    phases = [2, 3]
    while time.monotonic() < deadline:
        statuses = []
        for a in phases:
            now = time.monotonic()
            if now >= deadline:
                break
            dl = min(deadline, now + max(3.0, 0.5 * (deadline - now)))
            st = 'timeout'
            while time.monotonic() < dl:
                st = _search(a, d, D, rng, dl, best[0], consider, True)
                if st != 'ok':
                    break
            statuses.append(st)
        if statuses and all(s == 'exhausted' for s in statuses):
            break
        if not statuses:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
