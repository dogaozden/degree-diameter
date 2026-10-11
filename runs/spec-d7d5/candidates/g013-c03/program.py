import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (kept as fallbacks; exact for small D).
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
# New family: Haar-type bi-Cayley graphs over small groups G = Z_m x| Z_k2.
#
# Vertices A_g = g (0..G-1) and B_h = G + h. Edges A_g ~ B_{g*s} for s in S,
# where S is a set of d distinct group elements. Every vertex has degree d.
# Left translations are automorphisms, so the diameter is at most D iff a BFS
# from A_0 and a BFS from B_0 both reach all 2G vertices within D steps.
#
# Search: simulated annealing over the connection set S itself, with the
# number of unreached vertices as the cost. Each evaluation is a few
# vectorised numpy steps, so thousands of evaluations fit in the budget.
# The group order is pushed upward after each success.
# ----------------------------------------------------------------------------

_HAAR_ITERS = 6000
_HAAR_MAX_G = 1500


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = M[g, s] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _sample_group(target, rng):
    """Return (m, k2, r) with m*k2 in [target, target+3] for Z_m x| Z_k2, or None."""
    for _ in range(100):
        G = target + rng.randrange(0, 4)
        divs = [k for k in range(1, min(G, 48) + 1) if G % k == 0 and G // k >= 2]
        if not divs:
            continue
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        cands = [c for c in range(2, m)
                 if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if not cands:
            continue
        return m, k2, rng.choice(cands)
    return None


def _haar_cost(G, Ts, Invs, S, D):
    """Total unreached vertices from A_0 and from B_0 within D steps (0 means valid)."""
    Sa = np.asarray(S, dtype=np.int64)
    TS = Ts[Sa]    # TS[s, g] = g*s  (A -> B)
    IS = Invs[Sa]  # IS[s, h] = h*s^-1 (B -> A)
    total = 0
    for start_side in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[start_side][0] = True
        f = np.array([0], dtype=np.int64)
        cur = start_side
        for _ in range(D):
            tab = TS if cur == 0 else IS
            mark = np.zeros(G, dtype=bool)
            mark[tab[:, f].ravel()] = True
            tgt = 1 - cur
            new = mark & ~seen[tgt]
            seen[tgt] |= new
            f = np.nonzero(new)[0]
            cur = tgt
            if f.size == 0:
                break
        total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _haar_search(d, D, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over connection sets. Returns list S of d elements, or None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    cost = _haar_cost(G, Ts, Invs, S, D)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        pos = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[pos]
        S[pos] = new
        c2 = _haar_cost(G, Ts, Invs, S, D)
        temp = max(0.3, 0.05 * c0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[pos] = old
    return list(S) if cost == 0 else None


def _haar_edges(G, Ts, S):
    """Return (2G, edges) of the Haar graph with connection set S."""
    edges = []
    for s in S:
        col = Ts[s]
        for g in range(G):
            edges.append((g, G + int(col[g])))
    return 2 * G, edges


# ----------------------------------------------------------------------------

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

    # Exact constructions for small cases.
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

    # Main search: Haar graphs over small groups, pushing the order upward.
    while time.monotonic() < deadline:
        target = best_n // 2 + 1
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if G < d or G > _HAAR_MAX_G or G < target:
            continue
        S = _haar_search(d, D, G, Ts, Invs, rng, deadline, _HAAR_ITERS)
        if S is not None:
            n, e = _haar_edges(G, Ts, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
