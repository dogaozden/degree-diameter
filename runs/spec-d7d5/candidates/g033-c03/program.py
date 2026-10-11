import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families.
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


def _moore_half(d, D):
    """Half the Moore bound for bipartite graphs: the largest possible side size."""
    return sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# New family: Haar graphs over non-abelian groups Z_m x| Z_k, with a single
# connection set S (|S| = d) and a simulated-annealing search on S.
#
# Vertices: A_g = g (0 <= g < G), B_h = G + h. Edge A_g ~ B_{g*s} for s in S.
# Left multiplication is an automorphism, so the diameter equals
# max(ecc(A_e), ecc(B_e)); only two BFS runs are needed per candidate.
# WLOG the identity is in S (right-translating S gives an isomorphic graph),
# so S[0] = 0 is fixed.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k, r) with m*k = G and Z_m x| Z_k (r^k = 1 mod m), or None."""
    ks = [k for k in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24)
          if G % k == 0 and G // k >= 3]
    if not ks:
        return None
    k = rng.choice(ks)
    m = G // k
    r = 1
    if k > 1 and rng.random() < 0.7:
        for _ in range(200):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
    return m, k, r


def _mult_table(m, k, r):
    """Multiplication table M[x, y] = x*y for Z_m x|_r Z_k, element a*k + b."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return M


def _nbr_for(G, M, invs, S):
    """Neighbour table nbr[l, v] for the Haar graph with connection set S."""
    d = len(S)
    nbr = np.empty((d, 2 * G), dtype=np.int64)
    for l, s in enumerate(S):
        nbr[l, :G] = G + M[:, s]          # A_g ~ B_{g s}
        nbr[l, G:] = M[:, invs[s]]        # B_h ~ A_{h s^{-1}}
    return nbr


def _unreached(nbr, N, src, D):
    """Number of vertices not within distance D of src (frontier-based BFS)."""
    seen = np.zeros(N, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        nxt = nbr[:, frontier].ravel()
        nxt = nxt[~seen[nxt]]
        if nxt.size == 0:
            break
        nxt = np.unique(nxt)
        seen[nxt] = True
        frontier = nxt
    return N - int(seen.sum())


def _cost(G, M, invs, S, D):
    nbr = _nbr_for(G, M, invs, S)
    N = 2 * G
    return _unreached(nbr, N, 0, D) + _unreached(nbr, N, G, D)


def _anneal(d, D, G, M, invs, rng, deadline, iters):
    """Simulated annealing over connection sets S. Returns S with cost 0, or None."""
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _cost(G, M, invs, S, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - t / iters))
        pos = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        old = S[pos]
        S[pos] = new
        c2 = _cost(G, M, invs, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[pos] = old
    return S if cost == 0 else None


def _haar_edges(G, M, invs, S):
    nbr = _nbr_for(G, M, invs, S)
    edges = []
    for l in range(len(S)):
        edges.extend((g, int(v)) for g, v in enumerate(nbr[l, :G].tolist()))
    return edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(time_limit - 6.0, 0.9 * time_limit))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best_n, best_e = fallback
    try:
        # Exact D = 3 construction.
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
                best_n, best_e = pg
                if lib.is_prime_power(d - 1):
                    return best_n, best_e

        # Exact-ish D = 4 construction.
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None and gq[0] > best_n and lib.is_valid(gq[0], gq[1], d, D):
                best_n, best_e = gq
                if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                    return best_n, best_e

        # Haar-graph search over non-abelian groups.
        cap = min(_moore_half(d, D), 1600)
        best_G = best_n // 2
        step = max(2, best_G // 100)
        chunk = 3.0

        while time.monotonic() < deadline and best_G < cap:
            G = min(cap, best_G + 1 + rng.randrange(step))
            grp = _sample_group(G, rng)
            if grp is None:
                step = max(1, step // 2)
                continue
            m, k, r = grp
            M = _mult_table(m, k, r)
            invs = np.argmax(M == 0, axis=1)
            chunk_end = min(deadline, time.monotonic() + chunk)
            S = _anneal(d, D, G, M, invs, rng, chunk_end, 4000)
            if S is None:
                step = max(1, step // 2)
                continue
            edges = _haar_edges(G, M, invs, S)
            if 2 * G > best_n and lib.is_valid(2 * G, edges, d, D):
                best_n, best_e = 2 * G, edges
                best_G = G
    except Exception:
        pass

    if best_n > fallback[0] and lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return fallback
