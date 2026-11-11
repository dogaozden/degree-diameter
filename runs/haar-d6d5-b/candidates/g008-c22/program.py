"""Combined search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

Two constructions share one time budget:
  * Bi-Cayley graphs: four orbits of a group G of order N (4N vertices). N >= 172 beats the record 684.
  * Haar graphs: 2N vertices, searched over connection sets of size 6. Near-miss starts from earlier
    searches are tried first, then fresh metacyclic groups of order 344..372.

Every returned graph is checked with lib.is_valid. Fallbacks: a checked order-660 Haar graph, else K_{6,6}.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
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
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
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
    """Metacyclic parameters (m, k, lam) with m prime, k | m-1, lo <= m*k <= hi, lam^k = 1 mod m, lam != 1."""
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


# ------------------------------------------------------------------------ Haar graph search (cost via words)

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X."""
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


def haar_search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets with an optional start set. Returns (best S, best cost)."""
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = S0.copy() if S0 is not None else None, None, 0

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
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def haar_checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# -------------------------------------------------------------------------- bi-Cayley graph search

def _bc_nbr(MT, inv, N, S):
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


def _bc_cost(nbr, N):
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


def bc_search(MT, inv, N, deadline, rng):
    """Anneal the four connection sets until cost 0. Returns a checked (n, edges) or None."""
    n = 4 * N
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        keys = list(sizes)
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in keys}
        cur = _bc_cost(_bc_nbr(MT, inv, N, S), N)
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
            c = _bc_cost(_bc_nbr(MT, inv, N, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _bc_nbr(MT, inv, N, S)
            edges = [(int(u), int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _bc_candidates():
    """Non-abelian metacyclic groups of order 172..200 (smallest first), plus Heis(3) x Z_7 (order 189)."""
    out = []
    for NN in range(172, 201):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and lam % m != 1:
                    out.append(("meta", m, k, lam))
                    break
    out = out[:12]
    out.append(("heis", 3, 7, 0))
    return out


def _make_group(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_times_cyclic(group_heis(c[1]), c[2])


# ------------------------------------------------------------------------------------ fallbacks

def trivial(d, D):
    """Always-valid small graph for other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Checked order-660 Haar graph for d=6, D=5, else a trivial valid graph (K_{6,6} for d=6)."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = haar_checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def _keep(best, cand, d, D):
    """Replace best by cand if cand is larger and passes lib.is_valid."""
    if cand is None:
        return best
    n, edges = cand
    if n > best[0] and lib.is_valid(n, edges, d, D):
        return cand
    return best


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.78 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    p1 = t0 + 0.12 * budget   # Haar near-miss starts
    p2 = t0 + 0.60 * budget   # bi-Cayley candidates
    rng = np.random.default_rng(seed)
    best = _fallback(d, D)

    # Phase 1: Haar near-miss starts (2 short of valid at orders 351, 355; 4 short at 360).
    near = [
        (lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21]),
        (lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88]),
        (lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132]),
    ]
    for idx, (mk, S0) in enumerate(near):
        now = time.monotonic()
        if now >= p1:
            break
        end = now + (p1 - now) / (len(near) - idx)
        try:
            MT, inv = mk()
            S, c = haar_search(MT, inv, d, S0, end, rng)
            if S is not None and c == 0:
                best = _keep(best, haar_checked(MT, S, d, D), d, D)
        except Exception:
            pass

    # Phase 2: bi-Cayley graphs with four orbits (4N vertices, N >= 172 beats 684).
    cands = _bc_candidates()
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= p2:
            break
        end = now + (p2 - now) / (len(cands) - idx)
        try:
            MT, inv = _make_group(c)
            N = MT.shape[0]
            g = bc_search(MT, inv, N, end, rng)
            best = _keep(best, g, d, D)
        except Exception:
            pass

    # Phase 3: Haar graphs on fresh metacyclic groups of order 344..372 (random starts).
    fresh = meta_candidates(344, 372)[:4]
    for idx, (m, k, lam) in enumerate(fresh):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(fresh) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = haar_search(MT, inv, d, None, end, rng)
            if S is not None and c == 0:
                best = _keep(best, haar_checked(MT, S, d, D), d, D)
        except Exception:
            pass

    return best
