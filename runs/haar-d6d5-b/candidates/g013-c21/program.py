"""Bi-Cayley lift search plus the Haar-graph seed search for the bipartite degree-diameter problem (numpy only).

CHANGE IN THIS VERSION (bold): for the target (d=6, D=5) the primary construction is a multi-orbit group lift.
Take a finite group G of order N and a base bipartite graph with b vertices on each side, where the block
(i, j) carries a set S_ij of group elements.  Vertices (A_i, x) and (B_j, x) for x in G, with edges
(A_i, x) ~ (B_j, s*x) for s in S_ij.  Right multiplication is an automorphism, so every vertex is equivalent to one
of the 2b base vertices (x = identity).  The diameter is at most D iff each of the 2b base vertices reaches every
vertex within D steps, so the cost is the total number of unreached vertices from those 2b sources.  Orders
2bN in (684, 780] are searched with simulated annealing over the voltage sets (circulant block sizes, so every
vertex has degree d).  Only graphs passing lib.is_valid are kept.

The previous Haar-graph search is kept as a second tier, and the larger valid graph of the two is returned.
Non-target cases return a small always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

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


def group_agl(q, k=None):
    """GF(q) x| C_k: the maps t -> a*t + b on GF(q) with a in the subgroup of order k of GF(q)^* (default k = q-1,
    that is AGL(1, q)).  q a prime power (uses lib.GF).  The product is (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
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


# ------------------------------------------------------------------------------------------------ Haar search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j] (P an int array of pair products)."""
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
    """cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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
    """Score EVERY single-slot replacement of S (all slots x all group elements).  Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group.  With a start set S0: scan all its 1-swap neighbours first, then
    anneal from it, and restart from a perturbed S0 (half the time) or a random set when stuck.
    Returns (best S, best cost)."""
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


# --------------------------------------------------------------------------------------------- Haar graph

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def meta_candidates(lo, hi, exclude, limit):
    """Metacyclic Z_m x|_lam Z_k (non-abelian, lam != 1) with order N in (lo, hi], largest orders first."""
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


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, seconds-weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)
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
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ================================================================ bi-Cayley lift search (primary, target d6D5)

def _lift_adj(MT, b, blocks):
    """Adjacency lists of the lift.  A_i fibre i occupies [i*N, (i+1)*N); B_j fibre b+j occupies [(b+j)*N, ...)."""
    N = MT.shape[0]
    n = 2 * b * N
    adj = [[] for _ in range(n)]
    for (i, j), S in blocks.items():
        for s in S:
            row = MT[int(s)].tolist()
            for x in range(N):
                a = i * N + x
                c = (b + j) * N + row[x]
                adj[a].append(c)
                adj[c].append(a)
    return n, adj


def _lift_cost(n, adj, sources, D):
    """Total number of vertices NOT within distance D of the sources (summed over the sources)."""
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _lift_edges(MT, b, blocks):
    """Edge list of the lift (same convention as _lift_adj)."""
    N = MT.shape[0]
    xs = np.arange(N)
    out = []
    for (i, j), S in blocks.items():
        for s in S:
            tg = MT[int(s), xs].tolist()
            for x in range(N):
                out.append((i * N + x, (b + j) * N + tg[x]))
    return 2 * b * N, out


def _lift_sa(MT, b, c, d, D, rng, deadline, patience=900):
    """Anneal the voltage sets of a block circulant with block sizes c (c[k] for block offset k, sum c = d).
    Returns (best cost, best blocks)."""
    N = MT.shape[0]
    n = 2 * b * N
    keys = [(i, j) for i in range(b) for j in range(b) if c[(j - i) % b] > 0]
    sizes = {k: c[(k[1] - k[0]) % b] for k in keys}
    sources = [i * N for i in range(b)] + [(b + j) * N for j in range(b)]

    def fresh():
        return {k: [int(v) for v in rng.choice(N, sizes[k], replace=False)] for k in keys}

    def score(bl):
        return _lift_cost(n, _lift_adj(MT, b, bl)[1], sources, D)

    def copy_bl(bl):
        return {k: list(v) for k, v in bl.items()}

    blocks = fresh()
    cur = score(blocks)
    best, best_bl = cur, copy_bl(blocks)
    since = 0
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        k = keys[int(rng.integers(len(keys)))]
        S = blocks[k]
        p = int(rng.integers(len(S)))
        t = int(rng.integers(N))
        if t in S:
            continue
        old = S[p]
        S[p] = t
        new = score(blocks)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best:
                best, best_bl, since = cur, copy_bl(blocks), 0
                continue
        else:
            S[p] = old
        since += 1
        if since > patience:
            blocks = fresh()
            cur = score(blocks)
            since = 0
            if cur < best:
                best, best_bl = cur, copy_bl(blocks)
    return best, best_bl


def _lift_pool():
    """(group spec, order N, base size b) with lifted order 2bN in [688, 780] (above the record 684)."""
    pool = []
    for N in range(60, 200):
        for b in (2, 3, 4, 5):
            if not (688 <= 2 * b * N <= 780):
                continue
            for (m, k, lam) in meta_candidates(N - 1, N, set(), 3):
                pool.append((('meta', (m, k, lam)), N, b))
    pool.append((('sl25', None), 120, 3))
    pool.append((('heis5', None), 125, 3))
    return pool


def _lift_group(spec, cache):
    if spec not in cache:
        kind, arg = spec
        if kind == 'meta':
            MT = group_meta(*arg)[0]
        elif kind == 'sl25':
            MT = group_sl2(5)[0]
        else:
            MT = group_heis(5)[0]
        cache[spec] = MT
    return cache[spec]


def _lift_search(d, D, seed, deadline):
    """Random restarts over the pool.  Returns (n, edges) of the largest valid lift found, or None."""
    rng = np.random.default_rng(seed + 12345)
    pool = _lift_pool()
    if not pool:
        return None
    cache = {}
    best_n, best_edges = 0, None
    while time.monotonic() < deadline - 0.5:
        spec, N, b = pool[int(rng.integers(len(pool)))]
        try:
            c = [0] * b
            for _ in range(d):
                c[int(rng.integers(b))] += 1
            MT = _lift_group(spec, cache)
            slot = min(4.0, deadline - time.monotonic())
            cst, bl = _lift_sa(MT, b, c, d, D, rng, time.monotonic() + slot)
            if cst == 0:
                n, edges = _lift_edges(MT, b, bl)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n, best_edges = n, edges
        except Exception:
            continue
    return (best_n, best_edges) if best_edges is not None else None


# ======================================================================================== cell: d6D5
# Near-miss reconstruction: the 2-short Haar graphs of orders 351 and 355 (metacyclic) and a 4-short one of order 360 (SL(2,5) x Z_3), scan of all single swaps, then annealing from the near miss with perturbed restarts.
# Random-start searches over metacyclic groups of orders 331..342 come after the near misses.
TARGET = (6, 5)

# (name, group builder, start set S0 or None, share of the time budget).
PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3),
]


def _extra_plan():
    """Random-start tier: metacyclic groups of order 331..342 not already used above."""
    used = {(117, 3, 16), (71, 5, 5)}
    entries = []
    for m, k, lam in meta_candidates(330, 342, used, 6):
        entries.append((f'meta {m}/{k}/{lam} random', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 2))
    return entries


# Valid smaller Haar graph (order 330, 660 vertices), checked at run time.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    total = 0.82 * time_limit
    best = None
    # Primary: bi-Cayley lifts with 2..5 base vertices per side, lifted orders 688..780.
    try:
        best = _lift_search(d, D, seed, t0 + 0.55 * total)
    except Exception:
        best = None
    # Secondary: the Haar-graph search, with its checked fallback.
    remaining = t0 + total - time.monotonic()
    if remaining > 2.0:
        try:
            g2 = run(d, D, seed, remaining / 0.85, PLAN + _extra_plan(), FALLBACK)
            if g2 is not None and (best is None or g2[0] > best[0]):
                if lib.is_valid(g2[0], g2[1], d, D):
                    best = g2
        except Exception:
            pass
    if best is None:
        return trivial(d, D)
    return best
