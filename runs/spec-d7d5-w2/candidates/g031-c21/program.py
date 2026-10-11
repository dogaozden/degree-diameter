import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or near-exact families used as baselines and fallbacks.
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
# New construction: bipartite doubles of Cayley digraphs on non-abelian groups.
#
# For a finite group G and a set S of d distinct elements, the graph has
# A-vertices g (index g) and B-vertices h (index G + h), with edges
#     g ~ G + g*s           for s in S.
# This is the Haar-type lift over the group, with a single base pair and
# non-symmetric connection sets allowed. Left multiplication is an
# automorphism, so the diameter condition reduces to checking distances
# from the two base vertices (e, A) and (e, B). That is tracked with a
# 2-bit reach mask per vertex, which makes each evaluation cheap.
#
# Groups are Z_m semidirect Z_k with (a,b)(c,e) = (a + r^b c, b + e).
# The search is a simulated-annealing walk over S, minimising the number
# of unreached (source, vertex) pairs. When a group succeeds, the target
# order is raised and a new group is tried.
# ----------------------------------------------------------------------------

_GMAX = 2000
_KS = (1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24)


def _group_tables(m, k, r):
    """Return (G, MT, invs) for Z_m x| Z_k. MT[s, g] = g*s, invs[s] = s^{-1}."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    M = A * k + B  # M[x, y] = x * y
    MT = np.ascontiguousarray(M.T)
    invs = np.argmax(MT == 0, axis=1).astype(np.int64)  # g*s = identity (index 0)
    return G, MT, invs


def _row(G, MT, invs, s):
    """Neighbour list (length 2G) contributed by connection element s.

    A-vertex g -> G + g*s. B-vertex h -> h*s^{-1}.
    """
    return np.concatenate((G + MT[s], MT[invs[s]]))


def _cost(base, nbr, D, N2):
    """Return (unreached pairs, reach masks) for sources (e,A) bit 0 and (e,B) bit 1."""
    reach = base
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=0)
        if np.array_equal(new, reach):
            break
        reach = new
    got = int(np.sum(reach & 1)) + int(np.sum((reach >> 1) & 1))
    return 2 * N2 - got, reach


def _anneal(d, D, G, MT, invs, rng, deadline):
    """Search for a d-subset S of the group with diameter <= D. Returns S or None."""
    N2 = 2 * G
    base = np.zeros(N2, dtype=np.int64)
    base[0] = 1
    base[G] = 2
    S = rng.sample(range(G), d)
    nbr = np.empty((d, N2), dtype=np.int64)
    for l in range(d):
        nbr[l] = _row(G, MT, invs, S[l])
    cur, _ = _cost(base, nbr, D, N2)
    Sset = set(S)
    it = 0
    while cur > 0:
        it += 1
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        temp = 0.6 + 1.5 * max(0.0, 1.0 - it / 5000.0)
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in Sset:
            continue
        old = S[l]
        old_row = nbr[l].copy()
        nbr[l] = _row(G, MT, invs, new)
        c, _ = _cost(base, nbr, D, N2)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            S[l] = new
            Sset.discard(old)
            Sset.add(new)
        else:
            nbr[l] = old_row
    return S if cur == 0 else None


def _haar_edges(G, MT, S):
    """Edge list of the bipartite double: g ~ G + g*s for s in S."""
    edges = []
    gs = list(range(G))
    for s in S:
        col = (G + MT[s]).tolist()
        edges.extend(zip(gs, col))
    return edges


def _search(d, D, deadline, rng, start_G, consider):
    """Random group sampling with annealing; raises the target order when a group succeeds."""
    best_G = start_G
    while time.monotonic() < deadline:
        target = best_G + 1 + rng.randrange(0, max(1, best_G // 40 + 1))
        k = rng.choice(_KS)
        m = max(2, -(-target // k))
        if k == 1:
            r = 1
        else:
            r = None
            if k == 2 and rng.random() < 0.4:
                r = m - 1  # dihedral-type element, always valid for k = 2
            else:
                for _ in range(60):
                    c = rng.randrange(2, m) if m > 2 else 1
                    if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                        r = c
                        break
            if r is None:
                continue
        G_ = m * k
        if G_ > _GMAX or G_ < d:
            continue
        G, MT, invs = _group_tables(m, k, r)
        gdead = min(deadline, time.monotonic() + 2.5)
        S = _anneal(d, D, G, MT, invs, rng, gdead)
        if S is not None:
            if consider(2 * G, _haar_edges(G, MT, S)):
                best_G = G


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d, which is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Exact constructions: return immediately for calibration-style cases.
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

    # Main search. Any unexpected error leaves the best valid graph found so far.
    try:
        _search(d, D, deadline, rng, best_n // 2, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
