"""Mixed search for the bipartite degree-diameter problem at (d, D) = (6, 5).

Two constructions compete, and the largest valid graph is returned.

1. Haar graphs (kept from the parent). A Haar graph on a group G of order N with connection set S has 2N vertices and
   diameter at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Annealing over S finds these sets.

2. Group lifts of small bipartite base multigraphs (new). The base has k A-vertices and k B-vertices, each of
   degree d. Each dart (u, v, g) joins (u, x) to (v, x*g) for every x in G, so the lift has 2kN vertices and is
   d-regular. Left multiplication by G is an automorphism group acting transitively on each fibre. Therefore the
   diameter is at most D iff every one of the 2k base vertices at the identity fibre reaches all 2kN vertices within
   D steps. This gives a cheap cost (total unreached count over those 2k BFS runs) for annealing over the voltages.

Every returned graph is checked with lib.is_valid. If nothing valid beats the fallback, the largest valid graph wins.
Other (d, D) cases return a small valid construction immediately.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)


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
    """Table of a group given as an (N, c) integer coordinate array (element 0 is the identity)."""
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


# ------------------------------------------------------------------------------- Haar search (parent)

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
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
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * (deadline - time.monotonic()))
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
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def meta_candidates(lo, hi, exclude, limit):
    """Metacyclic Z_m x|_lam Z_k (lam != 1) with order N in (lo, hi], largest orders first."""
    out = []
    for N in range(hi, lo, -1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and (m, k, lam) not in exclude:
                    out.append((m, k, lam))
                    if len(out) >= limit:
                        return out
    return out


def run(d, D, rng, deadline_all, plan, fallback):
    """Run the Haar plan until deadline_all. Returns a checked valid graph or None."""
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    try:
        MT, _ = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return None


PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4),
    ('Heis(7), order 343', lambda: group_heis(7), None, 2),
]


def _extra_plan():
    used = {(117, 3, 16), (71, 5, 5)}
    entries = []
    for m, k, lam in meta_candidates(330, 342, used, 6):
        entries.append((f'meta {m}/{k}/{lam} random', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 2))
    return entries


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


# ------------------------------------------------------------------- group lifts of base multigraphs (new)

def lift_meta(N, limit):
    """Non-abelian metacyclic groups of order N as (m, k, lam) triples."""
    out = []
    for kk in range(2, N):
        if N % kk:
            continue
        m = N // kk
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, kk, m) == 1 % m:
                out.append((m, kk, lam))
                if len(out) >= limit:
                    return out
    return out


_GROUPS = {}


def get_group(key):
    if key not in _GROUPS:
        kind = key[0]
        if kind == 'meta':
            MT, _ = group_meta(key[1], key[2], key[3])
        elif kind == 'heis':
            MT, _ = group_heis(key[1])
        else:
            MT, _ = group_sl2(key[1])
        _GROUPS[key] = MT
    return _GROUPS[key]


def lift_configs(lo_n, hi_n):
    """(n, group key, group order N, k) with lo_n < 2kN <= hi_n, ascending in n, capped."""
    cfgs = []
    for key, N in [(('heis', 5), 125), (('sl2', 5), 120)]:
        for k in range(2, 12):
            n = 2 * k * N
            if lo_n < n <= hi_n:
                cfgs.append((n, key, N, k))
    for N in range(58, hi_n // 4 + 1):
        ks = [k for k in range(2, 13) if lo_n < 2 * k * N <= hi_n]
        if not ks:
            continue
        for m, kk, lam in lift_meta(N, 2):
            for k in ks:
                cfgs.append((2 * k * N, ('meta', m, kk, lam), N, k))
    cfgs.sort()
    return cfgs[:30]


def lift_search(MT, k, d, D, deadline, rng, patience=2500, T=0.8):
    """Anneal the voltages of a random d-regular bipartite base (k + k vertices) over the group table MT.
    Returns (U, V, G) with cost 0, or None if the deadline passes first."""
    N = MT.shape[0]
    E = k * d
    n = 2 * k * N
    x = np.arange(N)
    srcs = [u * N for u in range(k)] + [k * N + v * N for v in range(k)]

    def pick_g(exclude):
        while True:
            g = int(rng.integers(N))
            if g not in exclude:
                return g

    def init():
        U, V = [], []
        for _ in range(d):
            perm = rng.permutation(k)
            for u in range(k):
                U.append(u)
                V.append(int(perm[u]))
        U = np.array(U, dtype=np.int64)
        V = np.array(V, dtype=np.int64)
        G = np.zeros(E, dtype=np.int64)
        for i in range(E):
            taken = {int(G[j]) for j in range(i) if U[j] == U[i] and V[j] == V[i]}
            G[i] = pick_g(taken)
        return U, V, G

    def cost(U, V, G):
        A = (U[:, None] * N + x[None, :]).ravel()
        B = (k * N + V[:, None] * N + MT[x[None, :], G[:, None]]).ravel()
        src = np.concatenate([A, B])
        dst = np.concatenate([B, A])
        total = 0
        for s in srcs:
            reached = np.zeros(n, dtype=bool)
            reached[s] = True
            front = reached.copy()
            for _ in range(D):
                nxt = np.zeros(n, dtype=bool)
                nxt[dst[front[src]]] = True
                nxt &= ~reached
                if not nxt.any():
                    break
                reached |= nxt
                front = nxt
            total += n - int(reached.sum())
        return total

    U, V, G = init()
    cur = cost(U, V, G)
    best, since = cur, 0
    while True:
        if cur == 0:
            return U, V, G
        if time.monotonic() >= deadline:
            return None
        i = int(rng.integers(E))
        taken = {int(G[j]) for j in range(E) if j != i and U[j] == U[i] and V[j] == V[i]}
        old = int(G[i])
        G[i] = pick_g(taken | {old})
        c = cost(U, V, G)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cur = c
            if cur < best:
                best, since = cur, 0
        else:
            G[i] = old
        since += 1
        if since > patience:
            U, V, G = init()
            cur = cost(U, V, G)
            best, since = cur, 0


def lift_edges(MT, k, U, V, G):
    N = MT.shape[0]
    x = np.arange(N)
    A = (U[:, None] * N + x[None, :]).ravel()
    B = (k * N + V[:, None] * N + MT[x[None, :], G[:, None]]).ravel()
    return 2 * k * N, list(zip(A.tolist(), B.tolist()))


def lift_phase(d, D, rng, deadline):
    """Search lift configurations in ascending order of size; return the largest valid graph found, or None."""
    cfgs = lift_configs(684, 800)
    best = None
    for idx, (n_cfg, key, N, k) in enumerate(cfgs):
        now = time.monotonic()
        if now >= deadline:
            break
        if best is not None and n_cfg <= best[0]:
            continue
        left = len(cfgs) - idx
        end = min(deadline, now + max(0.6, (deadline - now) / left))
        try:
            MT = get_group(key)
            res = lift_search(MT, k, d, D, end, rng)
            if res is None:
                continue
            n, edges = lift_edges(MT, k, *res)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue
    return best


# ------------------------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    T = float(time_limit)
    rng = np.random.default_rng(seed)
    cands = []
    try:
        g = run(d, D, rng, t0 + 0.42 * T, PLAN + _extra_plan(), FALLBACK)
        if g is not None:
            cands.append(g)
    except Exception:
        pass
    try:
        g = lift_phase(d, D, rng, t0 + 0.80 * T)
        if g is not None:
            cands.append(g)
    except Exception:
        pass
    if not cands:
        return trivial(d, D)
    return max(cands, key=lambda g: g[0])
