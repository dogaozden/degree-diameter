import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured fallbacks (kept from the parent, all verified by lib.is_valid).
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
# New construction: single-base-vertex bi-Cayley graphs over finite groups,
# found by annealing the connection set.
#
# Vertices a_g and b_g for g in G. Connection set S (|S| = d) gives edges
# a_g ~ b_{g s} for s in S. Left translation by h maps a_g -> a_{hg}, b_g -> b_{hg}
# and is an automorphism, so distances from a_g equal distances from a_1 and
# distances from b_g equal distances from b_1. Hence the graph has diameter <= D
# iff both single-source balls (from a_1 and from b_1) cover everything within D.
# Normalising the identity into S (right-multiplying the B side) keeps the search
# space small. The cost (unreached vertices from the two sources) is evaluated
# with vectorised numpy BFS, so each evaluation costs well under a millisecond.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Full multiplication table of Z_m x|_r Z_k, element (a, b) coded a*k+b (same coding as lib.semidirect_group)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    A, B = x // k, x % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    return ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k


def _group_choices(G, rng, cap):
    """Candidate semidirect factorisations (m, k, r) with m * k = G, shuffled and capped."""
    out = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k = G // m
        if m == 1:
            out.append((1, k, 0))
            continue
        out.append((m, k, 1))  # direct product Z_m x Z_k (cyclic when coprime)
        if k >= 2:
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if rs:
                for r in rng.sample(rs, min(len(rs), 2)):
                    out.append((m, k, r))
    rng.shuffle(out)
    return out[:cap]


def _bicayley_cost(T, inv, S, G, D):
    """Number of (source, vertex) pairs unreached within D from a_1 and from b_1. Zero iff valid."""
    Sa = np.asarray(S, dtype=np.int64)
    Ia = inv[Sa]
    Aadj = T[:, Sa] + G   # a_g -> b_{g s}
    Badj = T[:, Ia]       # b_x -> a_{x s^-1}
    N = 2 * G
    cost = 0
    for src in (0, G):
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            fa = frontier[frontier < G]
            fb = frontier[frontier >= G] - G
            parts = []
            if fa.size:
                parts.append(Aadj[fa].ravel())
            if fb.size:
                parts.append(Badj[fb].ravel())
            if not parts:
                break
            nb = np.concatenate(parts)
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            frontier = nb
        cost += N - int(vis.sum())
    return cost


def _anneal_group(T, inv, G, d, D, rng, deadline):
    """Anneal a connection set S (identity included) on group G. Returns S with zero cost, or None."""

    def fresh():
        return [0] + rng.sample(range(1, G), d - 1)

    S = fresh()
    cur = _bicayley_cost(T, inv, S, G, D)
    best_local = cur
    stale = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        if stale > 600:
            S = fresh()
            cur = _bicayley_cost(T, inv, S, G, D)
            best_local = cur
            stale = 0
            continue
        i = rng.randrange(1, d)
        v = rng.randrange(1, G)
        if v in S:
            continue
        old = S[i]
        S[i] = v
        c2 = _bicayley_cost(T, inv, S, G, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / 1.5):
            cur = c2
        else:
            S[i] = old
        if cur < best_local:
            best_local = cur
            stale = 0
        else:
            stale += 1
    return S


def _bicayley_edges(T, G, S):
    """Edge list of the bi-Cayley graph: a_g ~ b_{g s} for s in S."""
    E = []
    for s in S:
        col = T[:, s]
        for g in range(G):
            E.append((g, G + int(col[g])))
    return 2 * G, E


def _bicayley_search(d, D, G_lo, G_hi, rng, deadline, consider):
    """Ascending sweep over group orders G; per G, anneal over several factorisations."""
    G = G_lo
    while G <= G_hi and time.monotonic() < deadline:
        choices = _group_choices(G, rng, 6)
        slice_t = min(1.5, max(0.0, deadline - time.monotonic()))
        for (m, k, r) in choices:
            now = time.monotonic()
            if now >= deadline:
                break
            sub = min(deadline, now + slice_t / max(1, len(choices)))
            T = _semidirect_table(m, k, r)
            inv = np.argmax(T == 0, axis=1)
            S = _anneal_group(T, inv, G, d, D, rng, sub)
            if S is not None:
                n, e = _bicayley_edges(T, G, S)
                consider(n, e)
                break
        G += 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases that already meet the Moore bound return immediately.
    if best_n >= moore:
        return best

    # Main search: bi-Cayley graphs over semidirect products, one base vertex per side.
    if d >= 2 and time.monotonic() < deadline:
        Mh = moore // 2
        G_lo = max(best_n // 2 + 1, d + 1, int(0.45 * Mh))
        G_hi = Mh
        try:
            _bicayley_search(d, D, G_lo, G_hi, rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
