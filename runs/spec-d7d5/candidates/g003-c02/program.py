import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact algebraic families (unchanged from the parent).
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
# ARM 1: random regular bipartite graphs repaired by edge-switch annealing.
#
# State: for each left vertex i, d slots; EB[i*d+s] is the right endpoint.
# Each column s is a permutation, so every right vertex has degree d.
# A move swaps the right endpoints of two random edges (preserves degrees).
# Cost = ordered unreachable pairs within distance D (bit-parallel over all
# vertices, one numpy gather per round) + penalty per duplicate edge.
# Left vertices are 0..n-1, right vertices are n..2n-1.
#
# Change: the ladder over side sizes now WARM-STARTS each larger size from the
# last solved graph, extended by adding one left and one right vertex per step
# (degree-preserving). The anneal then starts near a solution, with a cooler
# initial temperature, instead of from a random graph.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _rr_base(N, W):
    """Bitset rows: row v has only bit v set."""
    base = np.zeros((N, W), dtype=np.uint64)
    v = np.arange(N, dtype=np.int64)
    base[v, v // 64] = np.uint64(1) << (v % 64).astype(np.uint64)
    return base


def _rr_cost(n, d, EB, D, N, base):
    """Ordered unreachable pairs within distance D, plus duplicate-edge penalty."""
    E2 = EB.reshape(n, d)
    order = np.argsort(EB, kind="stable")
    nb = np.empty((N, d), dtype=np.int64)
    nb[:n] = n + E2
    nb[n:] = (order // d).reshape(n, d)
    R = base
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nb], axis=1)
    reached = int(_POP8[R.view(np.uint8)].sum())
    srt = np.sort(E2, axis=1)
    dup = int(np.count_nonzero(srt[:, 1:] == srt[:, :-1]))
    return N * N - reached + _PENALTY * dup


def _extend_eb(m, d, eb, rng):
    """Add left vertex m and right vertex m to an m-sided d-regular graph, keeping all degrees d.

    For each column s, a random left vertex a (distinct across columns) has its
    edge (a, b) replaced by (a, m) and (m, b), so the new vertices get degree d.
    """
    new = np.empty((m + 1) * d, dtype=np.int64)
    new[:m * d] = eb
    cols = rng.sample(range(m), d)
    for s in range(d):
        idx = cols[s] * d + s
        b = new[idx]
        new[idx] = m
        new[m * d + s] = b
    return new


def _grow_eb(eb, n_from, n_to, d, rng):
    """Extend a valid edge-array from n_from to n_to sides, one vertex pair at a time."""
    out = np.asarray(eb, dtype=np.int64)
    for m in range(n_from, n_to):
        out = _extend_eb(m, d, out, rng)
    return out


def _rr_search(n, d, D, rng, deadline, init=None):
    """Anneal an n+n vertex d-regular bipartite graph to diameter <= D.

    Returns (N, edges, EB) on success, else None. If init is given, start from it
    with a cooler temperature schedule.
    """
    N = 2 * n
    W = (N + 63) // 64
    base = _rr_base(N, W)
    if init is None:
        perms = [rng.sample(range(n), n) for _ in range(d)]
        EB = np.array(perms, dtype=np.int64).T.copy().ravel()
        t_hot = 8.0
    else:
        EB = np.array(init, dtype=np.int64).copy()
        t_hot = 2.0
    M = n * d
    cur = _rr_cost(n, d, EB, D, N, base)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur != 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t0) / span
        temp = t_hot * (0.03 ** frac) + 0.05
        e1 = rng.randrange(M)
        e2 = rng.randrange(M)
        if EB[e1] == EB[e2]:
            continue
        EB[e1], EB[e2] = EB[e2], EB[e1]
        c2 = _rr_cost(n, d, EB, D, N, base)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            EB[e1], EB[e2] = EB[e2], EB[e1]
    if cur != 0:
        return None
    E2 = EB.reshape(n, d).tolist()
    edges = set()
    for i in range(n):
        for j in E2[i]:
            edges.add((i, n + j))
    return N, sorted(edges), EB.copy()


def _rr_arm(d, D, rng, deadline):
    """Ladder over the side size n: warm-started growth while annealing succeeds, bisect after failure."""
    moore = 2 * sum((d - 1) ** i for i in range(D))
    cap = 1500
    side = max(d + 1, min(cap, int(0.3 * moore / 2)))
    lo = None
    lo_eb = None
    hi = None
    best = None
    init = None
    while time.monotonic() < deadline - 0.5:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(3.0, 0.3 * remaining))
        res = _rr_search(side, d, D, rng, slice_end, init)
        if res is not None:
            if best is None or res[0] > best[0]:
                best = (res[0], res[1])
            lo = side
            lo_eb = res[2]
            if side >= cap:
                break
            if hi is None:
                nxt = side + max(1, int(0.03 * side))
            else:
                if hi - lo <= 1:
                    break
                nxt = (lo + hi) // 2
        else:
            hi = side
            if lo is None:
                nxt = int(side * 0.94)
            else:
                if hi - lo <= 1:
                    break
                nxt = (lo + hi) // 2
        nxt = min(max(nxt, d + 1), cap)
        if lo is not None and nxt > lo:
            init = _grow_eb(lo_eb, lo, nxt, d, rng)
        else:
            init = None
        side = nxt
    if best is None:
        return None
    return best


# ----------------------------------------------------------------------------
# Parent's bi-Cayley lift search (kept as a second arm for leftover time).
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side."""
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = np.zeros((N, d), dtype=np.int64)

    def assign(l, i, s):
        j = layers[l][i]
        pm = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
        nb[i * G:(i + 1) * G, l] = (k + j) * G + pm
        inv = np.empty(G, dtype=np.int64)
        inv[pm] = ar
        nb[(k + j) * G:(k + j + 1) * G, l] = i * G + inv

    for l in range(d):
        for i in range(k):
            assign(l, i, S[l][i])

    base = np.zeros(N, dtype=np.int64)
    for r in range(k):
        base[r * G] = 1 << r
    for j in range(k):
        base[(k + j) * G] = 1 << (k + j)
    nreps = 2 * k

    def dup_count():
        seen = set()
        dup = 0
        for l in range(d):
            for i in range(k):
                key = (i, layers[l][i], S[l][i])
                if key in seen:
                    dup += 1
                else:
                    seen.add(key)
        return dup

    def cost():
        reach = base
        for _ in range(D):
            reach = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        reached = 0
        for r in range(nreps):
            reached += int(np.count_nonzero(reach & (1 << r)))
        return N * nreps - reached + _PENALTY * dup_count()

    cur = cost()
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        old_s = S[l][i]
        new_s = rng.randrange(G)
        assign(l, i, new_s)
        S[l][i] = new_s
        c2 = cost()
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            assign(l, i, old_s)
            S[l][i] = old_s

    if cur != 0:
        return None
    E = set()
    for x in range(N):
        for y in nb[x].tolist():
            if x != y:
                E.add((x, y) if x < y else (y, x))
    return N, sorted(E)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Arm 1: random regular bipartite graphs repaired by edge-switch annealing,
    # with warm-started growth over the side size.
    if D >= 3 and d >= 3 and time.monotonic() < deadline:
        rr_deadline = start + 0.6 * budget
        res = _rr_arm(d, D, rng, rr_deadline)
        if res is not None:
            consider(res[0], res[1])

    # Arm 2 (parent): bi-Cayley lifts over semidirect products, with leftover time.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        order, mul = g
        res = _search(d, D, k, order, mul, rng, deadline, 6000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
