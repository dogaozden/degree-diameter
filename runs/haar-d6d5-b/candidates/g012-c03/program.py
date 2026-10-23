"""Bold variant for d=6, D=5: lifts of a 2+2 base multigraph over groups of order 172..240.

Construction.  Let G be a finite group (table MT, identity 0).  Take base vertices A0, A1, B0, B1 and a
multiplicity pattern pat[i][j] with every row and column summing to d.  Each base pair (Ai, Bj) carries
pat[i][j] distinct voltages s in G, and the lift has edges (Ai, g) ~ (Bj, s*g).  The lift has 4|G| vertices,
is bipartite, and is d-regular.  Right multiplication by h is an automorphism, so the vertices of each fiber
are all equivalent.  The diameter is therefore at most D iff the BFS ball of radius D around the four fiber
identities covers the whole graph.  This gives a cheap cost (uncovered vertices from 4 roots).  Simulated
annealing over the voltages finds cost 0 for some group and pattern.  Every returned graph is checked with
lib.is_valid.  If nothing is found, the parent's valid Haar graph (660 vertices) is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, identity 0.  Needs lam^k = 1 mod m."""
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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
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
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------- 2+2 base lift machinery

PATTERNS = [
    [[3, 3], [3, 3]],
    [[4, 2], [2, 4]],
    [[5, 1], [1, 5]],
]


def build_adj(MT, inv, S):
    """Adjacency (4N x 6) of the lift.  Global ids: A_i fiber g -> i*N+g; B_j fiber k -> 2N+j*N+k."""
    N = MT.shape[0]
    g = np.arange(N, dtype=np.int64)
    A = np.empty((2 * N, 6), dtype=np.int64)
    B = np.empty((2 * N, 6), dtype=np.int64)
    for i in range(2):
        cols = 0
        for j in range(2):
            s = S[i][j]
            m = len(s)
            vals = MT[s[None, :], g[:, None]].astype(np.int64) + 2 * N + j * N
            A[i * N:(i + 1) * N, cols:cols + m] = vals
            cols += m
    for j in range(2):
        cols = 0
        for i in range(2):
            s = S[i][j]
            m = len(s)
            vals = MT[inv[s][None, :], g[:, None]].astype(np.int64) + i * N
            B[j * N:(j + 1) * N, cols:cols + m] = vals
            cols += m
    return np.vstack([A, B])


def _uncovered(ADJ, r, D, n):
    seen = np.zeros(n, dtype=bool)
    seen[r] = True
    frontier = np.array([r], dtype=np.int64)
    for _ in range(D):
        nb = ADJ[frontier].ravel()
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        seen[nb] = True
        frontier = nb
    return n - int(seen.sum())


def cost(MT, inv, S, D=5):
    """Uncovered vertices from the four fiber identities (0 = diameter <= D)."""
    N = MT.shape[0]
    ADJ = build_adj(MT, inv, S)
    n = 4 * N
    return sum(_uncovered(ADJ, r, D, n) for r in (0, N, 2 * N, 3 * N))


def _copy(S):
    return [[a.copy() for a in row] for row in S]


def _random_state(N, pat, rng):
    return [[rng.choice(N, pat[i][j], replace=False).astype(np.int64) for j in range(2)] for i in range(2)]


def anneal(MT, inv, pat, deadline, rng, temp=0.6, patience=6000):
    N = MT.shape[0]
    S = _random_state(N, pat, rng)
    cur = cost(MT, inv, S)
    best, bestc = _copy(S), cur
    since = 0
    while time.monotonic() < deadline and bestc > 0:
        if since > patience:
            S = _random_state(N, pat, rng)
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = _copy(S), cur
            continue
        k = int(rng.integers(4))
        i, j = divmod(k, 2)
        m = pat[i][j]
        t = int(rng.integers(m))
        x = int(rng.integers(N))
        if x in S[i][j]:
            since += 1
            continue
        old = S[i][j][t]
        S[i][j][t] = x
        c = cost(MT, inv, S)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c
            if c < bestc:
                best, bestc = _copy(S), c
                since = 0
            else:
                since += 1
        else:
            S[i][j][t] = old
            since += 1
    return best, bestc


def lift_edges(MT, inv, S):
    N = MT.shape[0]
    ADJ = build_adj(MT, inv, S)
    edges = []
    for u in range(2 * N):
        for v in ADJ[u]:
            edges.append((u, int(v)))
    return 4 * N, edges


def candidate_groups(rng):
    expl = [
        (189, lambda: group_times_cyclic(group_heis(3), 7)),
        (192, lambda: group_times_cyclic(group_sl2(3), 8)),
        (216, lambda: group_times_cyclic(group_agl(9), 3)),
        (220, lambda: group_times_cyclic(group_agl(11), 2)),
    ]
    meta = []
    for N in range(172, 201):
        for m in range(2, N):
            if N % m:
                continue
            k = N // m
            lam = next((l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1), None)
            if lam is None:
                continue
            meta.append((N, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    order = rng.permutation(len(meta))
    chosen = [meta[int(i)] for i in order[:10]]
    groups = expl + chosen
    groups.sort(key=lambda t: t[0])
    return groups


def search_base4(d, D, rng, deadline):
    groups = candidate_groups(rng)
    cache = {}
    while time.monotonic() < deadline:
        gi = int(rng.integers(len(groups)))
        pi = int(rng.integers(len(PATTERNS)))
        if gi not in cache:
            try:
                cache[gi] = groups[gi][1]()
            except Exception:
                cache[gi] = None
        grp = cache[gi]
        if grp is None:
            continue
        MT, inv = grp
        slice_end = min(deadline, time.monotonic() + 3.0)
        S, c = anneal(MT, inv, PATTERNS[pi], slice_end, rng)
        if c == 0:
            n, edges = lift_edges(MT, inv, S)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ------------------------------------------------------------------------------ fallbacks

def haar_checked(MT, S, d, D):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    edges = [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    if (d, D) != (6, 5):
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.7 * time_limit
    rng = np.random.default_rng(seed)
    res = None
    try:
        res = search_base4(d, D, rng, deadline)
    except Exception:
        res = None
    if res is not None:
        return res
    try:
        MT, _ = group_meta(33, 10, 26)
        g = haar_checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
