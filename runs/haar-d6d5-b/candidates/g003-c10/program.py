"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and connection set S (|S| = d), the Haar graph has vertices (g, A), (g, B)
and edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides; cost 0 = valid.

NEW IN THIS VERSION: RACING OVER GROUPS.  The parent annealed on four fixed groups, one after another, and
gave each a fixed time share.  Here every candidate group (the four families plus metacyclic groups
Z_m x|_lam Z_k of orders 331..372) gets a short annealing slice in the first round.  Each round keeps the
better half of the groups by best cost and gives the survivors longer slices (successive halving), so the
time goes to the groups that look closest to cost 0.  Any group that reaches cost 0 is built and checked with
lib.is_valid.  The program returns at once when a checked graph beats the record order 684, and otherwise
returns the largest checked graph found, falling back to a checked smaller Haar graph (order 330).
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


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
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


# ------------------------------------------------------------------------------------------------ search

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
    """Score EVERY single-slot replacement of S.  Returns (best cost, best S)."""
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


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000, scan=True):
    """Annealing over d-subsets of the group, from S0 (or random).  scan=True first tries all 1-swaps of S0.
    Returns (best S, best cost); best S is None if the deadline passed before any evaluation."""
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
        if scan:
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


# --------------------------------------------------------------------------------------------- the graph

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


# ------------------------------------------------------------------------- new: candidate groups and racing

RECORD_ORDER = 684   # a checked graph with more vertices than this beats the record; stop at once


def metacyclic_candidates(lo, hi, rng, cap):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, as (m, k, lam) triples.
    Larger orders come first; inside one order the triples are shuffled, and the list is capped."""
    found = []
    for N in range(hi, lo - 1, -1):
        block = []
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    block.append((m, k, lam))
        rng.shuffle(block)
        found.extend(block)
    return found[:cap]


def race(d, D, rng, t_end, builders):
    """Successive halving over candidate groups.  Each arm is (name, make_table).  Every round, each live arm
    anneals for a slice that grows each round; after round 0 the better half (by best cost) survives.
    Returns the largest checked valid graph found (or None), returning early once it beats RECORD_ORDER."""
    arms = []
    for name, make in builders:
        if time.monotonic() >= t_end:
            break
        try:
            MT, inv = make()
        except Exception:
            continue
        arms.append({"name": name, "MT": MT, "inv": inv, "S": None, "c": 10 ** 9, "dead": False})

    found = None
    rnd = 0
    while arms and time.monotonic() < t_end:
        if rnd >= 1 and len(arms) > 1:
            arms.sort(key=lambda a: a["c"])
            arms = arms[: max(1, (len(arms) + 1) // 2)]
        slice_s = min((t_end - time.monotonic()) / len(arms), 0.6 * 1.6 ** rnd)
        for arm in arms:
            now = time.monotonic()
            if now >= t_end:
                break
            if arm["dead"]:
                continue
            try:
                S, c = search(arm["MT"], arm["inv"], d, arm["S"], now + slice_s, rng, scan=False)
            except Exception:
                arm["dead"] = True
                continue
            if S is not None and c < arm["c"]:
                arm["S"], arm["c"] = S, c
            if arm["c"] == 0:
                arm["dead"] = True
                try:
                    g = checked(arm["MT"], arm["S"], d, D)
                except Exception:
                    g = None
                if g is not None:
                    if found is None or g[0] > found[0]:
                        found = g
                    if g[0] > RECORD_ORDER:
                        return found
        arms = [a for a in arms if not a["dead"]]
        rnd += 1
    return found


# ======================================================================================== cell: d6D5

TARGET = (6, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# Named families tried alongside the metacyclic candidates.
FAMILIES = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13)),
    ('Heis(7), order 343', lambda: group_heis(7)),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5)),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18)),
]

# Valid smaller Haar graph (order 330), checked at run time; always a safe floor.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    rng = np.random.default_rng(seed)
    t_end = time.monotonic() + 0.80 * time_limit

    best = None
    try:
        MT, inv = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    builders = list(FAMILIES)
    for m, k, lam in metacyclic_candidates(331, 372, rng, cap=16):
        builders.append((f"Z{m} x|Z{k}[{lam}]",
                         lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    try:
        g = race(d, D, rng, t_end, builders)
    except Exception:
        g = None
    if g is not None and (best is None or g[0] > best[0]):
        best = g
    return best if best is not None else trivial(d, D)
