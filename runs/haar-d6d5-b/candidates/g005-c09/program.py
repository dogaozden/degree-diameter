"""Combined (d=6, D=5) search: Haar graphs over non-abelian groups plus two-orbit group lifts.

Haar part: Haar graph on a group G of order |G| with a d-set S has 2|G| vertices and diameter <= 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Annealing over S, with batched one-slot cost updates, on
fresh metacyclic / Heisenberg(7) / SL(2,5)xZ_3 groups plus near-miss starts.

Lift part: two-orbit Z-style group lifts with 4M vertices (M in 172..200 to beat 684). Four BFS
sources suffice by left-multiplication symmetry. Simulated annealing over voltages.

Every returned graph is checked with lib.is_valid. A checked 660-vertex Haar graph is the fallback.
"""
import itertools
import math
import time
from math import gcd

import numpy as np

import lib

TARGET = (6, 5)


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Group table from an (N, c) coordinate array (identity first) and a vectorised product."""
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


def group_sl2(p):
    """SL(2, p) for prime p, matrices (a, b, c, d), identity first."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def meta_candidates(lo, hi, kmin=3, kmax=7):
    """Metacyclic (m, k, lam): m prime, k | m-1, lo <= m*k <= hi, lam of exact order k mod m."""
    out = []
    for k in range(kmin, kmax + 1):
        for m in range(3, hi // k + 1):
            if m * k < lo or not _is_prime(m) or (m - 1) % k:
                continue
            lam = next((r for r in range(2, m) if pow(r, k, m) == 1), None)
            if lam is None:
                continue
            out.append((m, k, lam))
    out.sort(key=lambda t: (t[0] * t[1], t[1]))
    return out


# ----------------------------------------------------------------------- Haar graph search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements on both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
        xi = inv[X]
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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score every single-slot replacement of S. Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of G. Returns (best S, best cost)."""
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = (S0.copy() if S0 is not None else None), None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
        if S1 is not None and c1 < bestc:
            best, bestc, S = S1.copy(), c1, S1.copy()
            if c1 == 0:
                return best, 0
    while time.monotonic() < deadline:
        if S is None:
            if S0 is not None and rng.random() < 0.5:
                S = S0.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
                S = random_set()
        if cur is None:
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
            S, cur = None, None
    return best, bestc


def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g,A) ~ (s*g,B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# --------------------------------------------------------------- two-orbit group lift search

PATTERNS = [
    [[3, 3], [3, 3]],
    [[2, 4], [4, 2]],
    [[4, 2], [2, 4]],
    [[1, 5], [5, 1]],
    [[5, 1], [1, 5]],
]


def build_nbr(MT, inv, M, volt):
    """Neighbour table (4M x 6). A-orbit i, B-orbit 2+j, dart (i,j,g)."""
    N = 4 * M
    nbr = np.empty((N, 6), dtype=np.int64)
    ar = np.arange(M, dtype=np.int64)
    ca = [0, 0]
    cb = [0, 0]
    for (i, j), vs in volt.items():
        for g in vs:
            nbr[i * M + ar, ca[i]] = (2 + j) * M + MT[ar, g]
            ca[i] += 1
            nbr[(2 + j) * M + ar, cb[j]] = i * M + MT[ar, inv[g]]
            cb[j] += 1
    return nbr


def lift_cost(nbr, N, M):
    """Uncovered vertices from the four orbit representatives within radius 5."""
    total = 0
    for s in (0, M, 2 * M, 3 * M):
        vis = np.zeros(N, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(5):
            nb = nbr[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += N - int(vis.sum())
    return total


def to_edges(MT, M, volt):
    ar = np.arange(M, dtype=np.int64)
    E = []
    for (i, j), vs in volt.items():
        for g in vs:
            u = i * M + ar
            v = (2 + j) * M + MT[ar, g]
            E.extend(zip(u.tolist(), v.tolist()))
    return 4 * M, [(int(a), int(b)) for a, b in E]


def search_group(MT, inv, M, deadline, rng, T=2.0, patience=4000):
    """Annealing over voltages with restarts. Returns a volt dict with cost 0, or None."""
    N = 4 * M
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        volt = {}
        for i in range(2):
            for j in range(2):
                c = pat[i][j]
                volt[(i, j)] = [int(x) for x in rng.choice(M, c, replace=False)] if c > 0 else []
        cur = lift_cost(build_nbr(MT, inv, M, volt), N, M)
        pairs = [p for p in volt if volt[p]]
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur == 0:
                return volt
            p = pairs[int(rng.integers(len(pairs)))]
            k = int(rng.integers(len(volt[p])))
            x = int(rng.integers(M))
            if x in volt[p]:
                since += 1
                continue
            old = volt[p][k]
            volt[p][k] = x
            c2 = lift_cost(build_nbr(MT, inv, M, volt), N, M)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                volt[p][k] = old
                since += 1
        if cur == 0:
            return volt
    return None


def lift_groups():
    """Metacyclic groups of order 172..200 (these give 4M > 684 vertices), smallest first."""
    out = []
    for m in range(3, 201):
        for k in range(2, 200 // m + 1):
            n_ = m * k
            if n_ < 172 or n_ > 200:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
                    break
    out.sort(key=lambda t: t[0])
    return out[:6]


# ------------------------------------------------------------------------------ plan

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    MT, _ = group_meta(33, 10, 26)
    return MT, FALLBACK_S


def _plan():
    """List of (kind, builder, aux, weight). kind 'haar' takes aux = start set or None; 'lift' ignores aux."""
    plan = []
    plan.append(('haar', lambda: group_heis(7), None, 1))                     # order 343 -> 686 vertices
    for m, k, lam in meta_candidates(344, 372)[:4]:
        plan.append(('haar', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1))
    plan += [
        ('haar', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 2),
        ('haar', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 2),
        ('haar', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 2),
    ]
    for _, builder in lift_groups():
        plan.append(('lift', builder, None, 1))
    return plan


# ---------------------------------------------------------------------------- fallback

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
    except Exception:
        pass
    try:
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline_all = t0 + budget
    rng = np.random.default_rng(seed)
    plan = _plan()
    total_w = sum(w for *_, w in plan)
    for kind, builder, aux, w in plan:
        now = time.monotonic()
        if deadline_all - now <= 0.5:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            if kind == 'haar':
                S, c = search(MT, inv, d, aux, end, rng)
                if S is not None and c == 0:
                    g = checked_haar(MT, S, d, D)
                    if g is not None:
                        return g
            else:
                M = MT.shape[0]
                volt = search_group(MT, inv, M, end, rng)
                if volt is not None:
                    n, edges = to_edges(MT, M, volt)
                    if lib.is_valid(n, edges, d, D):
                        return n, edges
        except Exception:
            continue
    try:
        MT, S = haar_fallback()
        g = checked_haar(MT, S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit)
