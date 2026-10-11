import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions kept from the parent (cheap, used for their cases).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _araujo_for(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: Haar graphs over nonabelian linear groups PSL/PGL(2, q).
#
# Vertices a_g = g and b_x = n + x for g, x in G. Connection set S (d distinct
# group elements): a_g ~ b_{g*s} for s in S. This is d-regular and bipartite.
# Left multiplication is an automorphism, so the distance from a_g to any vertex
# equals the distance from a_e to the translated vertex. Therefore a_e and b_e
# BFS-coverage within D suffices to certify the diameter.
# A nonabelian group gives far more distinct words than an abelian one, which is
# why this family can reach orders near the Moore-type ceiling.
# ----------------------------------------------------------------------------

def _linear_group(q, psl):
    """Return (T, invs, e) for PSL(2,q) (psl=True, q odd) or PGL(2,q), where T[g,h] = index(g*h)."""
    F = lib.GF(q)
    M, A = F.mul_table, F.add_table
    squares = {F.mul(x, x) for x in range(1, q)}
    els = []
    for a, b, c, dd in itertools.product(range(q), repeat=4):
        det = F.sub(F.mul(a, dd), F.mul(b, c))
        if det == 0:
            continue
        lead = next(x for x in (a, b, c, dd) if x)
        if lead != 1:  # projective normalisation
            continue
        if psl and det not in squares:
            continue
        els.append((a, b, c, dd))
    n = len(els)
    E = np.array(els, dtype=np.int64)
    keyidx = np.full(q ** 4, -1, dtype=np.int64)
    keys = ((E[:, 0] * q + E[:, 1]) * q + E[:, 2]) * q + E[:, 3]
    keyidx[keys] = np.arange(n)
    invs_field = np.array([0] + [F.inv(x) for x in range(1, q)], dtype=np.int64)
    a2, b2, c2, d2 = E[:, 0], E[:, 1], E[:, 2], E[:, 3]
    T = np.empty((n, n), dtype=np.int64)
    for i in range(n):
        a1, b1, c1, d1 = (int(x) for x in E[i])
        pa = A[M[a1, a2], M[b1, c2]]
        pb = A[M[a1, b2], M[b1, d2]]
        pc = A[M[c1, a2], M[d1, c2]]
        pd = A[M[c1, b2], M[d1, d2]]
        L = np.where(pa != 0, pa, np.where(pb != 0, pb, np.where(pc != 0, pc, pd)))
        sc = invs_field[L]
        na = M[sc, pa]
        nb = M[sc, pb]
        nc = M[sc, pc]
        nd = M[sc, pd]
        T[i] = keyidx[((na * q + nb) * q + nc) * q + nd]
    if (T < 0).any():
        return None
    e = int(keyidx[((1 * q + 0) * q + 0) * q + 1])
    invs = np.argmax(T == e, axis=1).astype(np.int64)
    return T, invs, e


def _nbr_matrix(T, invs, S):
    """Neighbour matrix (2n, d) of the Haar graph with connection set S."""
    n = T.shape[0]
    S = np.asarray(S, dtype=np.int64)
    A = n + T[:, S]          # a_g ~ b_{g s}
    B = T[:, invs[S]]        # b_x ~ a_{x s^{-1}}
    return np.vstack([A, B])


def _unreached(nbr, src, D):
    """Number of vertices not within distance D of src."""
    N2 = nbr.shape[0]
    seen = np.zeros(N2, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(D):
        nxt = nbr[front].ravel()
        nxt = np.unique(nxt[~seen[nxt]])
        if nxt.size == 0:
            break
        seen[nxt] = True
        front = nxt
    return N2 - int(seen.sum())


def _haar_search(T, invs, e, d, D, rng, deadline, iters, patience):
    """Local search for a connection set S of d distinct elements with diameter <= D. Returns S or None."""
    n = T.shape[0]
    srcs = (e, n + e)

    def cost_of(S):
        nb = _nbr_matrix(T, invs, S)
        return sum(_unreached(nb, s, D) for s in srcs)

    S = rng.sample(range(n), d)
    inS = set(S)
    cost = cost_of(S)
    c0 = float(max(cost, 1))
    best = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.5, 0.05 * c0 * (1.0 - t / iters))
        i = rng.randrange(d)
        new = rng.randrange(n)
        if new in inS:
            continue
        old = S[i]
        S[i] = new
        c2 = cost_of(S)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            inS.discard(old)
            inS.add(new)
            cost = c2
            if cost < best:
                best = cost
                last = t
        else:
            S[i] = old
    return list(S) if cost == 0 else None


def _haar_edges(T, S):
    n = T.shape[0]
    S = np.asarray(S, dtype=np.int64)
    cols = T[:, S]
    rows = np.repeat(np.arange(n, dtype=np.int64), len(S))
    return list(zip(rows.tolist(), (cols.ravel() + n).tolist()))


# ----------------------------------------------------------------------------
# Driver.
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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3:
            ar = _araujo_for(d)
            if ar is not None:
                consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Haar graphs over nonabelian linear groups PSL/PGL(2, q).
    groups = []
    for q in (4, 5, 7, 8, 9, 11, 13):
        po = q * (q * q - 1)
        groups.append((q, False, po))
        if q % 2 == 1:
            groups.append((q, True, po // 2))

    dead = set()
    cache = {}
    while time.monotonic() < deadline:
        active = [g for g in groups
                  if g[2] >= d and 2 * g[2] > best_n and g[2] <= 2400 and g not in dead]
        if not active:
            break
        spec = rng.choice(active)
        if spec not in cache:
            grp = _linear_group(spec[0], spec[1])
            if grp is None:
                dead.add(spec)
                continue
            cache[spec] = grp
        T, invs, e = cache[spec]
        S = _haar_search(T, invs, e, d, D, rng, deadline, 4000, 700)
        if S is not None:
            consider(2 * T.shape[0], _haar_edges(T, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
