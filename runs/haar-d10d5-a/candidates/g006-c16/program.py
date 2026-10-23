"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a d-subset of G.  The Haar graph has vertices (g, A) and (g, B) for
g in G and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G| vertices.  Its
diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements of
both sides, and cost 0 means valid.

THIS VERSION.  The search adds a new move, TARGETED PROPOSALS.  For slot i, the uncovered elements t of
each side suggest candidate values that cover t directly:
  side 0: x = s_j * t^-1 gives x^-1 s_j = t,
  side 1: x = t^-1 * s_j gives s_j x^-1 = t,
for a random other slot j.  Half of each batch of candidates comes from these targeted moves and half is
uniform random.  Any cost-0 graph is checked with lib.is_valid before it is returned, and the fallback
is always a checked graph.
"""
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


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j] (P an int array of elements)."""
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


def uncovered_elements(MT, inv, S):
    """Return [uncovered elements on side 0, uncovered elements on side 1] as index arrays."""
    N = MT.shape[0]
    out = []
    for P in _pairs(MT, inv, S):
        cov = _cover(MT, N, np.unique(P))
        out.append(np.nonzero(~cov)[0])
    return out


def proposals(MT, inv, S, i, K, rng):
    """Candidate replacements for slot i: about half target uncovered elements, the rest are uniform random.

    A targeted candidate for uncovered t on side 0 is x = s_j * t^-1 (so x^-1 s_j = t).
    On side 1 it is x = t^-1 * s_j (so s_j x^-1 = t).  The slot j is chosen at random among the other slots.
    """
    N = MT.shape[0]
    rest = np.delete(S, i)
    n_t = K // 2
    pool0, pool1 = uncovered_elements(MT, inv, S)
    parts = []
    if len(pool0) + len(pool1) > 0 and n_t > 0:
        allt = np.concatenate([pool0, pool1]).astype(np.int64)
        lab = np.concatenate([np.zeros(len(pool0), dtype=np.int64), np.ones(len(pool1), dtype=np.int64)])
        picks = rng.integers(0, len(allt), size=n_t)
        t = allt[picks]
        sd = lab[picks]
        s = rest[rng.integers(0, len(rest), size=n_t)]
        x0 = MT[s, inv[t]]
        x1 = MT[inv[t], s]
        parts.append(np.where(sd == 0, x0, x1).astype(np.int32))
    n_r = K - (sum(len(p) for p in parts))
    parts.append(rng.integers(0, N, size=n_r).astype(np.int32))
    X = np.concatenate(parts).astype(np.int32)
    X = X[~np.isin(X, rest)]
    return np.unique(X)


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group, using targeted and random proposals.
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
        X = proposals(MT, inv, S, i, K, rng)
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
    cands = [lib.haar_graph(d, range(d)),
             (2 * d, [(i, d + j) for i in range(d) for j in range(d)])]   # K_{d,d}: diameter 2
    for n, edges in cands:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return cands[-1]


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, seconds-weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
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


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Metacyclic Z_m x|_lam Z_k of order m*k in [2000, 2100] (above 2000 is needed to beat the record of 4000).
META_SPECS = [(101, 20), (41, 50), (29, 70), (31, 65), (61, 33), (79, 26), (131, 16)]


def _meta_builder(m, k):
    lam = next((l for l in range(2, m) if pow(l, k, m) == 1), None)
    if lam is None:
        return None
    return lambda: group_meta(m, k, lam)


def _build_plan():
    plan = []
    for m, k in META_SPECS:
        b = _meta_builder(m, k)
        if b is not None:
            plan.append((f'Z{m} x| Z{k}', b, None, 1))
    return plan


PLAN = _build_plan()

# Valid smaller Haar graph, checked at run time; used only when no plan entry reaches cost 0.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        g = run(d, D, seed, time_limit, PLAN, FALLBACK)
        if lib.is_valid(g[0], g[1], d, D):
            return g
    except Exception:
        pass
    return trivial(d, D)
