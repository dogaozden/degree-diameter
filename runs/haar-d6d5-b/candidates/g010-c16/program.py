"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

Stage 1 (new, bold): multi-orbit lifts.  Take 2b base vertices (b on side A, b on side B) and d "slots".
Slot k joins A-base i to B-base sig[k][i] through group element G[k][i], where sig[k] is a permutation.
The lift has 2*b*|G| vertices: (i, x) ~ (b + sig[k][i], x*G[k][i]).  Left multiplication by any h in G is an
automorphism, so the diameter is at most 5 iff a BFS of depth 5 from (r, e) reaches every vertex, for each of
the 2b base vertices r.  Simulated annealing moves single group labels and slot permutations.  Each candidate
is checked with lib.is_valid before it is returned.

Stage 2 (parent): Haar graphs (1 A-base, 1 B-base) found by annealing on connection sets, with the near-miss
plan and the random-start metacyclic tier.  It runs with the remaining budget.

If neither stage finds a valid graph, the parent's always-valid fallback is returned.  Cases other than the
target return the small always-valid graph.
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
    """Heisenberg group mod p, order p^3."""
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


def group_agl(q, k=None):
    """GF(q) x| C_k, the affine maps t -> a*t + b with a in the subgroup of order k of GF(q)^*."""
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


# ------------------------------------------------------------------------------ parent Haar search

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
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def meta_candidates(lo, hi, exclude, limit):
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


# ------------------------------------------------------------- new: multi-orbit lifts

def _multi_lift_adj(MT, inv, sig, G, b, d):
    """Adjacency (2*b*N, d).  A-base i is i, B-base j is b+j.  Slot k: (i, x) ~ (b+sig[k,i], x*G[k,i])."""
    N = MT.shape[0]
    x = np.arange(N)
    adj = np.empty((2 * b * N, d), dtype=np.int64)
    for k in range(d):
        for i in range(b):
            adj[i * N:(i + 1) * N, k] = (b + sig[k, i]) * N + MT[x, G[k, i]]
        invs = np.argsort(sig[k])
        for j in range(b):
            i = int(invs[j])
            gi = inv[G[k, i]]
            adj[(b + j) * N:(b + j + 1) * N, k] = i * N + MT[x, gi]
    return adj


def _multi_cost(adj, N, nb, D):
    """Unreached (base rep, vertex) pairs, summed over all 2b base representatives (identity element is index 0)."""
    n = adj.shape[0]
    c = 0
    for r in range(nb):
        src = r * N
        reach = np.zeros(n, dtype=bool)
        reach[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = adj[front].ravel()
            nxt = nxt[~reach[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            reach[nxt] = True
            front = nxt
        c += n - int(reach.sum())
    return c


def _multi_edges(MT, inv, sig, G, b, d):
    N = MT.shape[0]
    adj = _multi_lift_adj(MT, inv, sig, G, b, d)
    us = np.repeat(np.arange(b * N), d)
    vs = adj[:b * N].ravel()
    pairs = set(zip(us.tolist(), vs.tolist()))
    return 2 * b * N, sorted(pairs)


def multi_anneal(MT, inv, b, d, D, deadline, rng, temp=1.0, patience=3000):
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        sig = np.array([rng.permutation(b) for _ in range(d)], dtype=np.int64)
        G = rng.integers(0, N, size=(d, b)).astype(np.int64)
        cur = _multi_cost(_multi_lift_adj(MT, inv, sig, G, b, d), N, 2 * b, D)
        if cur < bestc:
            best, bestc = (sig.copy(), G.copy()), cur
        if cur == 0:
            return best, 0
        since = 0
        while since < patience and time.monotonic() < deadline:
            sig2, G2 = sig.copy(), G.copy()
            k = int(rng.integers(d))
            if rng.random() < 0.7:
                i = int(rng.integers(b))
                G2[k, i] = rng.integers(N)
            else:
                a, a2 = rng.choice(b, 2, replace=False)
                sig2[k, [a, a2]] = sig2[k, [a2, a]]
            cc = _multi_cost(_multi_lift_adj(MT, inv, sig2, G2, b, d), N, 2 * b, D)
            delta = cc - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                sig, G, cur = sig2, G2, cc
                if cur < bestc:
                    best, bestc = (sig.copy(), G.copy()), cur
                    since = 0
                    if cur == 0:
                        return best, 0
            since += 1
    return best, bestc


def _groups_of_order(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for lam in range(1, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
    return out


def multi_stage(d, D, seed, deadline):
    rng = np.random.default_rng(seed + 7919)
    list2, list3 = [], []
    for N in range(172, 186):          # b = 2: 4N vertices, need 4N > 684
        for (m, k, lam) in _groups_of_order(N):
            list2.append((2, N, m, k, lam))
    for N in range(115, 123):          # b = 3: 6N vertices, need 6N > 684
        for (m, k, lam) in _groups_of_order(N):
            list3.append((3, N, m, k, lam))
    list2 = [list2[i] for i in rng.permutation(len(list2))]
    list3 = [list3[i] for i in rng.permutation(len(list3))]
    jobs = []
    for i in range(max(len(list2), len(list3))):
        if i < len(list2):
            jobs.append(list2[i])
        if i < len(list3):
            jobs.append(list3[i])
    for (b, N, m, k, lam) in jobs:
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = min(deadline, now + 4.0)
        try:
            MT, inv = group_meta(m, k, lam)
            best, c = multi_anneal(MT, inv, b, d, D, slice_end, rng)
        except Exception:
            continue
        if best is not None and c == 0:
            sig, G = best
            n, edges = _multi_edges(MT, inv, sig, G, b, d)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ======================================================================================== cell: d6D5
TARGET = (6, 5)

PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3),
]


def _extra_plan():
    used = {(117, 3, 16), (71, 5, 5)}
    entries = []
    for m, k, lam in meta_candidates(330, 342, used, 6):
        entries.append((f'meta {m}/{k}/{lam} random', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 2))
    return entries


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    try:
        res = multi_stage(d, D, seed, t0 + 0.42 * time_limit)
    except Exception:
        res = None
    if res is not None:
        return res
    remaining = 0.9 * time_limit - (time.monotonic() - t0)
    plan = PLAN + _extra_plan()
    return run(d, D, seed, max(remaining, 1.0), plan, FALLBACK)
