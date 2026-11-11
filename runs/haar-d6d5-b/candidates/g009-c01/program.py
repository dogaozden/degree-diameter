"""Combined search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

Two constructions share one time budget:
  1. Haar graphs H(G, S) with |G| >= 343 (2|G| > 684 vertices). Vertices (g,A), (g,B), edges (g,A) ~ (s*g,B).
     Diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G, so the search minimises the uncovered elements.
  2. Bi-Cayley (two-orbit) graphs over a group G of order N >= 172 (4N > 684 vertices). Four orbits
     A_0, A_1, B_0, B_1 with connection sets S_ij of sizes a, 6-a, 6-a, a. Diameter <= 5 iff BFS of radius 5
     from the four base vertices covers all vertices.

Each job is an annealing search; every returned graph is checked with lib.is_valid. The largest valid graph wins,
and a checked order-660 Haar graph is the fallback.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q):
    """AGL(1, q) for a prime power q: maps t -> a*t + b, product (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
    F = lib.GF(q)
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in range(1, q) if (b, a) != (0, 1)], dtype=np.int64)
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


# ------------------------------------------------------------------------------- Haar search (cost)

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(S_i^-1 S_j, S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X (only the words involving slot i are recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
        if side == 0:
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Anneal a d-subset (containing the identity) toward cost 0. Returns (S, cost); S is None if nothing was tried."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S = None
    return best, bestc


def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# ------------------------------------------------------------------------ bi-Cayley search (cost)

def _nbr(MT, inv, N, S):
    """Neighbour array (4N x DEG). Orbits: A_0 = 0..N-1, A_1 = N..2N-1, B_0 = 2N..3N-1, B_1 = 3N..4N-1.
    A_i(g) ~ B_j(g*s) for s in S[(i, j)]."""
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, DEG), dtype=np.int64)
    for i in (0, 1):
        c = 0
        for j in (0, 1):
            for s in S[(i, j)]:
                nbr[i * N:(i + 1) * N, c] = (2 + j) * N + MT[g, s]
                c += 1
    for j in (0, 1):
        c = 0
        for i in (0, 1):
            for s in S[(i, j)]:
                nbr[(2 + j) * N:(3 + j) * N, c] = i * N + MT[g, inv[s]]
                c += 1
    return nbr


def _bi_cost(nbr, N):
    """Vertices not reached within DIAM steps from the four base vertices (0 means diameter <= DIAM)."""
    n = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nbr[fr].ravel()
            nx = np.unique(nx[~seen[nx]])
            if nx.size == 0:
                break
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


def _bi_search(MT, inv, N, deadline, rng):
    """Anneal the four connection sets to cost 0; return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        keys = list(sizes)
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in keys}
        cur = _bi_cost(_nbr(MT, inv, N, S), N)
        stall = 0
        T = 0.6
        while time.monotonic() < deadline and cur > 0 and stall < 4000:
            key = keys[int(rng.integers(4))]
            pos = int(rng.integers(sizes[key]))
            x = int(rng.integers(N))
            if x in S[key]:
                stall += 1
                continue
            newS = dict(S)
            arr = S[key].copy()
            arr[pos] = x
            newS[key] = arr
            c = _bi_cost(_nbr(MT, inv, N, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _nbr(MT, inv, N, S)
            n = 4 * N
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _bi_candidates():
    """Non-abelian metacyclic groups of order in [172, 200], plus Heis(3) x Z_7 (order 189)."""
    out = []
    for NN in range(172, 201):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and pow(lam, 1, m) != 1:
                    out.append(("meta", m, k, lam))
                    break
    out = out[:8]
    out.append(("heis", 3, 7, 0))
    return out


def _make_bi(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_times_cyclic(group_heis(c[1]), c[2])


# ------------------------------------------------------------------------------------ jobs and build

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def _haar_job(builder):
    def job(end, rng):
        MT, inv = builder()
        S, c = search(MT, inv, DEG, end, rng)
        if S is not None and c == 0:
            return checked(MT, S, DEG, DIAM)
        return None
    return job


def _bi_job(cand):
    def job(end, rng):
        MT, inv = _make_bi(cand)
        return _bi_search(MT, inv, MT.shape[0], end, rng)
    return job


HAAR_GROUPS = [
    lambda: group_times_cyclic(group_heis(3), 13),   # order 351
    lambda: group_heis(7),                           # order 343
    lambda: group_times_cyclic(group_agl(9), 5),     # order 360
    lambda: group_times_cyclic(group_agl(5), 18),    # order 360
]


def _jobs():
    haar = [_haar_job(b) for b in HAAR_GROUPS]
    bi = [_bi_job(c) for c in _bi_candidates()]
    jobs = []
    for k in range(max(len(haar), len(bi))):
        if k < len(haar):
            jobs.append(haar[k])
        if k < len(bi):
            jobs.append(bi[k])
    return jobs


def _schedule(jobs, t_end, rng):
    """Run jobs one after another, sharing the remaining time equally. Returns the largest valid graph found."""
    best = None
    for idx, job in enumerate(jobs):
        now = time.monotonic()
        if now >= t_end:
            break
        end = now + (t_end - now) / (len(jobs) - idx)
        try:
            g = job(end, rng)
        except Exception:
            g = None
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    return best


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.8 * time_limit, time_limit - 8.0))
    t_end = t0 + budget
    rng = np.random.default_rng(seed)
    best = _fallback(d, D)
    found = _schedule(_jobs(), t_end, rng)
    if found is not None and found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
        best = found
    return best
