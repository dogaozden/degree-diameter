"""Haar-graph search for the bipartite degree-diameter problem, diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S (|S| = d), the Haar graph has vertices (g, A), (g, B)
and edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides.

NEW IN THIS VERSION.
  * Targeted moves.  Random replacements are mixed with proposals aimed at uncovered elements.  For an
    uncovered t on the A side, a slot x covers t directly when x = s t^-1 or x = s t (s any other slot).
    On the B side, x = t s or x = t^-1 s.  The annealer scores these together with random candidates.
  * Successive-halving race.  Many groups of order just above 2000 (metacyclic Z_m x| Z_k and Heisenberg
    mod 13, order 2197) are searched in parallel.  Each round gives every surviving group a doubled time
    slice, warm-started from its best set, then keeps the better half.  Time goes to the groups that look
    closest to cost 0.
  * Every returned graph is checked with lib.is_valid.  A valid smaller Haar graph is the fallback.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity)."""
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


# ------------------------------------------------------------------------------------------- scoring

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements on both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = MT[Si[:, None], S[None, :]].ravel()
    P1 = MT[S[:, None], Si[None, :]].ravel()
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in (P0, P1))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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


# ------------------------------------------------------------------------- NEW: targeted candidates

def targeted_candidates(MT, inv, S, rng, m=6):
    """Replacement values that would directly cover a few uncovered elements.

    Side 0 word x^-1 s = t gives x = s t^-1, and s^-1 x = t gives x = s t.
    Side 1 word x s^-1 = t gives x = t s, and s x^-1 = t gives x = t^-1 s.
    Returns a flat int array of candidates (may repeat; may hit slots already in S).
    """
    N = MT.shape[0]
    Si = inv[S]
    cov0 = _cover(MT, N, np.unique(MT[Si[:, None], S[None, :]].ravel()))
    cov1 = _cover(MT, N, np.unique(MT[S[:, None], Si[None, :]].ravel()))
    out = []
    for cov, side in ((cov0, 0), (cov1, 1)):
        unc = np.nonzero(~cov)[0]
        if len(unc) == 0:
            continue
        for t in rng.choice(unc, min(m, len(unc)), replace=False):
            t = int(t)
            ti = int(inv[t])
            if side == 0:
                out.append(MT[S, ti])
                out.append(MT[S, t])
            else:
                out.append(MT[t, S])
                out.append(MT[ti, S])
    return np.concatenate(out).astype(np.int32) if out else np.empty(0, dtype=np.int32)


# ------------------------------------------------------------------------------------------- search

def search(MT, inv, d, S0, deadline, rng, K=32, temp=0.45, patience=3000):
    """Annealing over d-subsets, mixing random and targeted replacement candidates.
    Restarts from a perturbed best (half the time) or a random set when stuck.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S = None if S0 is None else np.array(S0, dtype=np.int32).copy()
    cur, since = None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            if best is not None and rng.random() < 0.5:
                S = best.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
                S = random_set()
            cur = None
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        rest = np.delete(S, i)
        rnd = rng.integers(0, N, size=K // 2).astype(np.int32)
        tg = targeted_candidates(MT, inv, S, rng)
        if len(tg) > K // 2:
            tg = rng.choice(tg, K // 2, replace=False)
        X = np.unique(np.concatenate([rnd, tg.astype(np.int32)]))
        X = X[~np.isin(X, rest)]
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
        since += 1
        if since > patience:
            S = None
    return best, bestc


# ------------------------------------------------------------------------------- NEW: successive race

def race(d, D, rng, deadline, cands):
    """Successive-halving race over several groups.  Each round gives each surviving group a time slice
    (doubling every round), warm-started from its best set, then keeps the better half.
    cands: list of (name, group builder, S0 or None).  Returns a checked graph or None."""
    states = []
    for name, builder, S0 in cands:
        if time.monotonic() >= deadline:
            break
        try:
            MT, inv = builder()
            S = None if S0 is None else np.array(S0, dtype=np.int32)
            c = 10 ** 9
            if S is not None:
                c = cost(MT, inv, S)
                if c == 0:
                    g = checked(MT, S, d, D)
                    if g is not None:
                        return g
        except Exception:
            continue
        states.append({'MT': MT, 'inv': inv, 'S': S, 'c': c, 'dead': False})

    slice_t = 0.6
    while states and time.monotonic() < deadline:
        for st in states:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_t)
            try:
                S, c = search(st['MT'], st['inv'], d, st['S'], end, rng)
            except Exception:
                st['dead'] = True
                continue
            if S is not None and c < st['c']:
                st['S'], st['c'] = S, c
            if st['c'] == 0:
                g = checked(st['MT'], st['S'], d, D)
                if g is not None:
                    return g
                st['dead'] = True
        states = [s for s in states if not s['dead']]
        states.sort(key=lambda s: s['c'])
        if len(states) > 1:
            states = states[:max(1, len(states) // 2)]
        slice_t *= 2
    return None


# --------------------------------------------------------------------------------------------- graph

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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def metacyclic_list(lo, hi, count):
    """(N, m, k, lam) for metacyclic Z_m x| Z_k with N = m*k in [lo, hi], lam^k = 1 mod m, lam != 1, smallest first."""
    found = []
    for N in range(lo, hi + 1):
        for k in range(2, 11):
            if N % k:
                continue
            m = N // k
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    found.append((N, m, k, lam))
                    break
    found.sort()
    return found[:count]


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Near miss from earlier searches: Z_401 x| Z_5 (order 2005, 6 short of cost 0).
NEAR_S0 = [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957]

# Valid smaller Haar graph (checked at run time), used only if the race finds nothing.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)
    try:
        cands = [('near 401/5/39', lambda: group_meta(401, 5, 39), NEAR_S0)]
        for N, m, k, lam in metacyclic_list(2001, 2060, 7):
            cands.append((f'meta {m}/{k}/{lam}',
                          lambda m=m, k=k, lam=lam: group_meta(m, k, lam), None))
        cands.append(('heis13', lambda: group_heis(13), None))
        g = race(d, D, rng, deadline, cands)
    except Exception:
        g = None
    if g is not None:
        return g
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
