"""Two-orbit group lifts for the bipartite degree-diameter problem at (d=10, D=5).

Bold change: the target case no longer searches Haar graphs (one orbit per side). It searches
two-orbit lifts over a group G of order M in roughly [901, 1150]. The graph has 4 orbits
(A0, A1, B0, B1), each of size M, so it has 4M vertices, which beats 4000 when M >= 1001.
Vertex A_i,g is i*M+g and vertex B_j,h is 2M+j*M+h. The edges are A_i,g ~ B_j,(s*g) for s in S_ij,
with |S_ij| = 5 for every (i, j), so every vertex has degree 10.

Right multiplication by any h in G is an automorphism, and it is transitive on each orbit. So the
graph has diameter <= 5 iff the BFS from (identity, A_i) and from (identity, B_j) reaches everything
within 5 steps, for all four orbits. cost(S) is the total number of unreached vertices over those four
BFS runs, and cost 0 means valid. Annealing moves one element of one S_ij at a time.

Safety: a valid Haar fallback (order 1791, 3582 vertices) is computed first and verified with lib.is_valid.
A two-orbit result replaces it only if it is larger and passes lib.is_valid. Other cases use verified
small graphs.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table (MT[a, b] = index of a*b)."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b, a in the subgroup of order k of GF(q)^*."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- two-orbit lift search

SIZE = 5          # |S_ij|: each block has degree 2*5 = 10
PATIENCE = 400    # non-improving moves before a restart


def cost(MT, inv, S):
    """Total unreached vertices over BFS (depth 5) from one representative of each of the four orbits.
    S[i][j] is an int64 array of 5 group elements. Cost 0 means diameter <= 5."""
    M = MT.shape[0]
    Si = [[inv[S[i][j]] for j in range(2)] for i in range(2)]
    total = 0
    for src in range(4):
        f = np.zeros((4, M), dtype=bool)
        r = np.zeros((4, M), dtype=bool)
        f[src, 0] = True
        r[src, 0] = True
        for _ in range(5):
            nf = np.zeros((4, M), dtype=bool)
            for i in range(2):
                g = np.flatnonzero(f[i])
                if g.size:
                    for j in range(2):
                        nf[2 + j, MT[S[i][j][:, None], g[None, :]].ravel()] = True
            for j in range(2):
                h = np.flatnonzero(f[2 + j])
                if h.size:
                    for i in range(2):
                        nf[i, MT[Si[i][j][:, None], h[None, :]].ravel()] = True
            nf &= ~r
            r |= nf
            f = nf
            if not f.any():
                break
        total += 4 * M - int(r.sum())
    return total


def anneal(MT, inv, deadline, rng):
    """Simulated annealing with random restarts. Returns a cost-0 set system or None at the deadline."""
    M = MT.shape[0]
    while time.monotonic() < deadline:
        S = [[rng.choice(M, SIZE, replace=False).astype(np.int64) for _ in range(2)] for _ in range(2)]
        cur = cost(MT, inv, S)
        if cur == 0:
            return S
        local, since = cur, 0
        while time.monotonic() < deadline and since < PATIENCE:
            i = int(rng.integers(2))
            j = int(rng.integers(2))
            t = int(rng.integers(SIZE))
            x = int(rng.integers(M))
            arr = S[i][j]
            if x in arr:
                continue
            old = int(arr[t])
            arr[t] = x
            new = cost(MT, inv, S)
            delta = new - cur
            temp = max(1.0, 0.01 * cur)
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = new
                if cur == 0:
                    return S
                if cur < local:
                    local, since = cur, 0
                else:
                    since += 1
            else:
                arr[t] = old
                since += 1
    return None


def two_orbit_edges(M, S):
    """Edges of the two-orbit lift: A_i,g = i*M+g, B_j,h = 2M+j*M+h, A_i,g ~ B_j,(s*g)."""
    g = np.arange(M)
    return 4 * M, S  # placeholder replaced below


def build_two_orbit(MT, S):
    """Return (n, edges) for the two-orbit lift with connection sets S."""
    M = MT.shape[0]
    edges = []
    g = np.arange(M)
    for i in range(2):
        for j in range(2):
            for s in S[i][j]:
                a = i * M + g
                b = 2 * M + j * M + MT[int(s), g].astype(np.int64)
                edges.extend(zip(a.tolist(), b.tolist()))
    return 4 * M, edges


# --------------------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def fallback_graph(d, D):
    """The verified Haar graph of order 1791 (3582 vertices) for (10, 5)."""
    MT, _ = group_meta(199, 9, 180)
    S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e
    if D >= 2 and d >= 1:
        e = [(i, d + j) for i in range(d) for j in range(d)]
        if lib.is_valid(2 * d, e, d, D):
            return 2 * d, e
    if D >= 1 and d >= 1:
        return 2, [(0, 1)]
    return 1, []


# ------------------------------------------------------------------------------------ candidate groups

def _primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def _element_of_order(p, k):
    """An element of exact order k in Z_p^*, for prime p and k | p-1."""
    for a in range(2, p):
        if pow(a, k, p) == 1 and all(pow(a, j, p) != 1 for j in range(1, k)):
            return a
    return None


def candidate_groups(lo=901, hi=1150):
    """(order, name, builder) for groups of order in [lo, hi], largest first."""
    out = []
    for p in _primes_upto(hi):
        for k in range(2, p):
            if (p - 1) % k == 0 and lo <= p * k <= hi:
                lam = _element_of_order(p, k)
                if lam is not None:
                    out.append((p * k, f"meta {p}x|{k}",
                                lambda p=p, k=k, lam=lam: group_meta(p, k, lam)))
    for q, k in [(31, 30), (32, 31), (43, 21), (47, 23), (49, 24)]:
        if lo <= q * k <= hi:
            out.append((q * k, f"AGL-sub({q},{k})", lambda q=q, k=k: group_agl(q, k)))
    if lo <= 7 * 6 * 24 <= hi:
        pass
    if lo <= 336 * 3 <= hi:
        out.append((336 * 3, "SL(2,7)xZ3", lambda: group_times_cyclic(group_sl2(7), 3)))
    if lo <= 343 * 3 <= hi:
        out.append((343 * 3, "Heis7xZ3", lambda: group_times_cyclic(group_heis(7), 3)))
    out.sort(key=lambda t: -t[0])
    return out


# ------------------------------------------------------------------------------------------ driver

def build_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = min(0.7 * time_limit, 40.0)
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        best = fallback_graph(d, D)
    except Exception:
        best = None
    best_n = best[0] if best is not None else 0

    cands = candidate_groups()
    for idx, (M_order, name, builder) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        if 4 * M_order <= best_n:
            continue
        slice_end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = builder()
        except Exception:
            continue
        try:
            S = anneal(MT, inv, slice_end, rng)
        except Exception:
            S = None
        if S is None:
            continue
        try:
            n, edges = build_two_orbit(MT, S)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best, best_n = (n, edges), n
        except Exception:
            pass
    return best


def build(d, D, seed, time_limit):
    try:
        if (d, D) == (10, 5):
            res = build_target(d, D, seed, time_limit)
            if res is not None:
                return res
            fb = fallback_graph(d, D)
            if fb is not None:
                return fb
        return trivial(d, D)
    except Exception:
        return trivial(d, D)
