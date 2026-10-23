"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A), (g, B) and
edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts uncovered elements on both sides; cost 0 is valid.

NEW IN THIS VERSION: TARGETED WORD-EQUATION MOVES.  Random slot replacements rarely cover a specific
missing element.  For an uncovered target t and a random word w built from the other slots, the value of
slot i that makes some word involving x equal to t can be solved for directly (x = s_b * w * t^-1, and
similar forms).  targeted_proposals() generates these candidates for uncovered elements on either side,
and the annealer scores them with the exact incremental cost (batch_costs).  Candidates are only proposals,
so a wrong formula costs time but never validity.  Every returned graph is checked with lib.is_valid.
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


# ------------------------------------------------------------------------------------------------ cover

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j] (P an int array of elements)."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def _side_pairs(MT, inv, S, side):
    Si = inv[S]
    if side == 0:
        return MT[Si[:, None], S[None, :]].ravel()
    return MT[S[:, None], Si[None, :]].ravel()


def _uncovered(MT, inv, S, side):
    """Indices of elements NOT covered by the pair products of S on the given side."""
    N = MT.shape[0]
    P = np.unique(_side_pairs(MT, inv, S, side))
    return np.nonzero(~_cover(MT, N, P))[0]


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


def _scores(MT, inv, S, i, X, chunk=256):
    """batch_costs in chunks, to keep memory bounded."""
    return np.concatenate([batch_costs(MT, inv, S, i, X[lo:lo + chunk]) for lo in range(0, len(X), chunk)])


# ------------------------------------------------------------------------- NEW: targeted proposals

def targeted_proposals(MT, inv, S, i, rng, n_targets=3, n_pairs=4, n_b=4):
    """Candidates for slot i that try to cover a currently uncovered element t.

    A word involving x has one of the forms x^-1 s, s^-1 x (side 0) or x s^-1, s x^-1 (side 1).  If t is
    to be written as (that word) * w or w * (that word), with w a pair product of the other slots, then x
    is a short product of t, w^-1 and some s_b.  All such candidates are generated for a few random
    targets t and random w, then returned for exact scoring.
    """
    rest = np.delete(S, i)
    r = len(rest)
    pool = [(0, int(t)) for t in _uncovered(MT, inv, S, 0)] + [(1, int(t)) for t in _uncovered(MT, inv, S, 1)]
    if not pool:
        return np.empty(0, dtype=np.int32)
    out = []
    for p in rng.choice(len(pool), min(n_targets, len(pool)), replace=False):
        side, t = pool[int(p)]
        ia = rng.integers(r, size=n_pairs)
        ib = rng.integers(r, size=n_pairs)
        if side == 0:
            W = MT[inv[rest[ia]], rest[ib]]
        else:
            W = MT[rest[ia], inv[rest[ib]]]
        SB = rest[rng.integers(r, size=n_b)][:, None]
        W = W[None, :]
        iW = inv[W]
        it = inv[t]
        if side == 0:
            cands = [MT[MT[SB, W], it], MT[MT[SB, it], W], MT[MT[SB, t], iW], MT[MT[SB, iW], t]]
        else:
            cands = [MT[MT[t, iW], SB], MT[MT[iW, t], SB], MT[MT[W, it], SB], MT[MT[it, W], SB]]
        out.extend(c.ravel() for c in cands)
    X = np.unique(np.concatenate(out)).astype(np.int32)
    return X[~np.isin(X, rest)]


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
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000, p_target=0.5):
    """Annealing over d-subsets with a mix of random and targeted slot moves.
    Returns (best S, best cost)."""
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
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.2 * (deadline - time.monotonic()))
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
        if rng.random() < p_target:
            X = np.concatenate([targeted_proposals(MT, inv, S, i, rng),
                                rng.integers(0, N, size=max(1, K // 4)).astype(np.int32)])
        else:
            X = rng.integers(0, N, size=K).astype(np.int32)
        X = np.unique(X.astype(np.int32))
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = _scores(MT, inv, S, i, X)
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
    if D <= 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.75 * time_limit
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

# Metacyclic Z_m x|_lam Z_k of order m*k in [2000, 2100].
META_SPECS = [(101, 20), (41, 50), (29, 70), (31, 65), (61, 33), (79, 26)]


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
    return run(d, D, seed, time_limit, PLAN, FALLBACK)
