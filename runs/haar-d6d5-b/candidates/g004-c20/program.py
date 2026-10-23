"""Bold variant for d=6, D=5: 2x2 base-graph voltage lifts over metacyclic groups, searched by annealing.

THEORY.  Let G be a finite group with multiplication table MT (element 0 = identity), and let the
base graph have two A-vertices and two B-vertices, with d darts from each A-vertex and d darts into
each B-vertex.  Dart t joins class A_i and class B_j with voltage s_t.  The lift has vertices
(A_i, g) and (B_j, h) for g, h in G, and edges (A_i, g) ~ (B_j, s_t * g).  Right multiplication by any
h in G is an automorphism that fixes each class, so every vertex of a class is equivalent to its
identity element.  Hence diameter <= D iff a BFS of depth D from one representative per class
reaches every vertex.  The cost is the total number of unreached (representative, vertex) pairs, and
the graph is valid exactly when the cost is 0.  The lift has 4|G| vertices, so |G| >= 172 beats the
record 684.

PLAN.  (1) Anneal voltages and a random A/B dart pattern over metacyclic groups of order 172..230,
smallest first, keeping the largest valid lift.  (2) Run the Haar-graph search from the earlier code.
(3) Compare everything against a verified fallback Haar graph of 660 vertices.  Every returned graph
passes lib.is_valid, and any exception falls back to a small always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
LIFT_LO, LIFT_HI = 172, 230


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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)."""
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
    """Metacyclic parameters (m, k, lam) with m prime, k | m-1, lo <= m*k <= hi, lam of exact order k mod m."""
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


# ------------------------------------------------------------------------------- Haar-graph search (old)

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
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
    """Score every single-slot replacement of S.  Returns (best cost, best S)."""
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
    """Annealing over d-subsets of the group, with optional start set S0.  Returns (best S, best cost)."""
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
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def haar_search(d, D, rng, deadline, plan):
    """Run the Haar plan entries in order, sharing the time until deadline.  Returns a checked graph or None."""
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) * w / total_w
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
    return None


def _target_plan():
    """Fresh metacyclic groups of order 344..372 (random starts), then the earlier near-miss entries."""
    fresh = []
    for m, k, lam in meta_candidates(344, 372):
        fresh.append((f'meta {m}/{k}/{lam}',
                      (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1))
        if len(fresh) == 4:
            break
    near = [
        ('meta 117/3/16, order 351', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 2),
        ('meta 71/5/5, order 355', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 2),
        ('SL(2,5) x Z_3, order 360', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 2),
    ]
    return fresh + near


# Verified fallback: a valid Haar graph with 660 vertices.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


# ---------------------------------------------------------------- 2x2 base-graph voltage lifts (new)

def build_nbr(MT, inv, N, V, pat, d):
    """Neighbour array (4N, d) of the 2x2-base lift.  A_i vertex g = i*N + g; B_j vertex h = 2N + j*N + h.
    Dart t of pattern (i, j) with voltage s joins (A_i, g) to (B_j, s*g)."""
    ar = np.arange(N)
    rowsA = [[], []]
    rowsB = [[], []]
    for t, (i, j) in enumerate(pat):
        s = int(V[t])
        rowsA[i].append(2 * N + j * N + MT[s, ar].astype(np.int64))
        rowsB[j].append(i * N + MT[int(inv[s]), ar].astype(np.int64))
    nbr = np.empty((4 * N, d), dtype=np.int64)
    for i in range(2):
        nbr[i * N:(i + 1) * N] = np.stack(rowsA[i], axis=1)
    for j in range(2):
        nbr[2 * N + j * N:2 * N + (j + 1) * N] = np.stack(rowsB[j], axis=1)
    return nbr


def lift_cost(nbr, N, D):
    """Total unreached (representative, vertex) pairs within distance D, over the 4 class representatives."""
    n = nbr.shape[0]
    tot = 0
    for c in range(4):
        reach = np.zeros(n, dtype=bool)
        reach[c * N] = True
        for _ in range(D):
            nxt = reach | reach[nbr].any(axis=1)
            if np.array_equal(nxt, reach):
                break
            reach = nxt
        tot += n - int(reach.sum())
    return tot


def anneal_lift(MT, inv, N, d, deadline, rng, D=5):
    """Anneal voltages and the dart pattern (x, d-x, d-x, x) for one group.  Returns (cost, pattern, voltages)."""
    def fresh():
        x = int(rng.integers(1, d))
        pat = [(0, 0)] * x + [(0, 1)] * (d - x) + [(1, 0)] * (d - x) + [(1, 1)] * x
        V = rng.integers(0, N, size=2 * d).astype(np.int64)
        return pat, V

    pat, V = fresh()
    cur = lift_cost(build_nbr(MT, inv, N, V, pat, d), N, D)
    T, stall = 1.5, 0
    while cur > 0 and time.monotonic() < deadline:
        t = int(rng.integers(2 * d))
        old = int(V[t])
        V[t] = int(rng.integers(N))
        c = lift_cost(build_nbr(MT, inv, N, V, pat, d), N, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            if c < cur:
                stall = 0
            cur = c
        else:
            V[t] = old
        stall += 1
        T = max(0.3, T * 0.9995)
        if stall > 3000:
            pat, V = fresh()
            cur = lift_cost(build_nbr(MT, inv, N, V, pat, d), N, D)
            T, stall = 1.5, 0
    return cur, pat, V


def lift_graph(MT, inv, N, pat, V, d):
    """Simple graph of the lift (duplicate darts merged)."""
    nbr = build_nbr(MT, inv, N, V, pat, d)
    n = 4 * N
    es = set()
    for v in range(n):
        for u in nbr[v].tolist():
            if u != v:
                es.add((v, u) if v < u else (u, v))
    return n, sorted(es)


def lift_search(d, D, rng, deadline, floor_n):
    """Try metacyclic groups of order in [LIFT_LO, LIFT_HI], smallest first, and return the largest valid lift
    with more than floor_n vertices, or None."""
    best = None
    best_n = floor_n
    cands = meta_candidates(LIFT_LO, LIFT_HI, kmin=3, kmax=7)
    for idx, (m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        left = len(cands) - idx
        end = now + (deadline - now) / left
        N = m * k
        if 4 * N <= best_n:
            continue
        try:
            MT, inv = group_meta(m, k, lam)
            c, pat, V = anneal_lift(MT, inv, N, d, end, rng, D)
        except Exception:
            continue
        if c == 0:
            try:
                n, edges = lift_graph(MT, inv, N, pat, V, d)
            except Exception:
                continue
            if n > best_n and lib.is_valid(n, edges, d, D):
                best, best_n = (n, edges), n
    return best


# ----------------------------------------------------------------------------------------------- build

def _build_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.8 * time_limit
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, inv = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    floor_n = best[0] if best is not None else 0
    g = lift_search(d, D, rng, t0 + 0.6 * total, floor_n)
    if g is not None and (best is None or g[0] > best[0]):
        best = g

    g = haar_search(d, D, rng, t0 + total, _target_plan())
    if g is not None and (best is None or g[0] > best[0]):
        best = g

    return best if best is not None else trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return _build_target(d, D, seed, time_limit)
    except Exception:
        return trivial(d, D)
