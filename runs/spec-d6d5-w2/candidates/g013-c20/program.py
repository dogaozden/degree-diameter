import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Small-D baselines (valid for every D at least their diameter).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d. Diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 (q prime power >= 3). Diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q). Diameter 4."""
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cyclic Haar graphs H(Z_G, S) for D >= 5.
#
# Vertices A_x = x and B_y = G + y. A_x ~ B_{x+s} for s in S, |S| = d.
# Translating S does not change the graph, so we fix 0 in S.
# The swap A_x <-> B_{-x} is an automorphism, and translations act transitively
# on each side, so diameter <= D holds iff the ball of radius D around A_0
# covers all 2G vertices. That is the cost used by the search.
# ----------------------------------------------------------------------------

def _haar_cost(G, S, D):
    """Number of vertices not within distance D of A_0. Zero means the diameter condition holds."""
    Sa = np.asarray(S, dtype=np.int64)
    seen = np.zeros(2 * G, dtype=bool)
    seen[0] = True
    front = np.array([0], dtype=np.int64)
    for _ in range(D):
        fa = front[front < G]
        fb = front[front >= G] - G
        parts = []
        if fa.size:
            parts.append(((fa[:, None] + Sa[None, :]) % G + G).ravel())
        if fb.size:
            parts.append(((fb[:, None] - Sa[None, :]) % G).ravel())
        if not parts:
            break
        nb = np.unique(np.concatenate(parts))
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        seen[nb] = True
        front = nb
    return 2 * G - int(np.count_nonzero(seen))


def _anneal_haar(G, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S (0 in S, |S| = d). Returns S or None."""
    if G < d:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _haar_cost(G, S, D)
    T = 2.0
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        T = max(0.05, T * 0.999)
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _haar_cost(G, S2, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = S2, c2
    return S if c == 0 else None


def _haar_edges(G, S):
    return 2 * G, [(x, G + (x + s) % G) for x in range(G) for s in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    best_box = [best]

    def consider(n, e):
        if n > best_box[0][0] and lib.is_valid(n, e, d, D):
            best_box[0] = (n, e)

    if D == 2:
        return best_box[0]

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        return best_box[0]

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best_box[0]

    # D >= 5: cheap valid baselines first, then the cyclic Haar search.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    if d >= 3:
        rng = random.Random(seed * 7919 + d * 101 + D)
        target = max(d, best_box[0][0] // 2 + 1)
        best_haar = None
        fails = 0
        iters = 3000
        while time.monotonic() < deadline:
            S = _anneal_haar(target, d, D, rng, deadline, iters)
            if S is not None:
                best_haar = (target, S)
                target += 1
                fails = 0
                iters = 3000
            else:
                fails += 1
                iters = min(iters * 2, 60000)
                if fails >= 6:
                    # Move on to a larger order; keep the last successful one.
                    target += 1
                    fails = 0
                    iters = 3000
        if best_haar is not None:
            G, S = best_haar
            n, e = _haar_edges(G, S)
            consider(n, e)

    if not lib.is_valid(best_box[0][0], best_box[0][1], d, D):
        return lib.haar_graph(d, range(d))
    return best_box[0]
