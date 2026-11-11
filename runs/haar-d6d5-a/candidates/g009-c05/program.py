"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a d-subset of G.  The Haar graph has vertices (g, A) and (g, B) for g in G,
with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G| vertices.  Its diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the group elements left uncovered by these two
word sets; cost 0 means a valid graph.

WHAT THIS FILE DOES.  Builds a plan of non-abelian groups (fixed families plus metacyclic Z_m x| Z_k groups of
orders 343..372, then order 342 as a safety net).  All candidates are time-sliced round-robin with growing slices.
Each candidate keeps its annealing state (current set, cost, best set, stall counter) between slices, so a slice
resumes the trajectory instead of restarting from a random set.  Annealing with K random replacements per step and
an incremental cost drives each group toward cost 0.  The first group that reaches cost 0 is built and checked with
lib.is_valid.  If nothing succeeds, a precomputed valid smaller Haar graph (order 330, 660 vertices) is returned.
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
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


def metacyclic_candidates(lo, hi, per_pair, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi (up to per_pair lam values per (m, k))."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if lam % m != 1 and math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    cnt += 1
                    if cnt >= per_pair:
                        break
            if len(out) >= limit:
                return out
    return out


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]].ravel())
    P1 = np.unique(MT[S[:, None], Si[None, :]].ravel())
    return (N - int(_cover(MT, N, P0).sum())) + (N - int(_cover(MT, N, P1).sum()))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X (only slot-i words are recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
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


def new_state():
    """Persistent annealing state for one group: current set, its cost, best set seen, stall counter."""
    return {'S': None, 'cur': None, 'since': 0, 'best': None, 'bestc': 10 ** 9}


def search(MT, inv, d, deadline, rng, st, K=24, temp=0.45, patience=4000):
    """Simulated-annealing style local search over d-subsets of the group, resuming from state st.
    The state persists across time slices, so the trajectory is not reset between slices.
    Returns (best S, best cost) seen so far for this group."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if st['S'] is None:
            st['S'] = random_set()
            st['cur'] = None
        if st['cur'] is None:
            st['cur'] = cost(MT, inv, st['S'])
            st['since'] = 0
            if st['cur'] < st['bestc']:
                st['best'], st['bestc'] = st['S'].copy(), st['cur']
            if st['cur'] == 0:
                return st['best'], 0
        S = st['S']
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - st['cur']
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            st['cur'] = int(cs[j])
            if st['cur'] < st['bestc']:
                st['best'], st['bestc'], st['since'] = S.copy(), st['cur'], 0
                if st['cur'] == 0:
                    return st['best'], 0
            elif delta < 0:
                st['since'] = 0
        st['since'] += 1
        if st['since'] > patience:
            st['S'], st['cur'] = None, None
    return st['best'], st['bestc']


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


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder); candidates are time-sliced round-robin with growing slices.
    Each candidate keeps its search state across slices.
    fallback: (builder, S) of a valid smaller Haar graph."""
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    cache = {}
    states = {}
    slice_len = 0.5
    while time.monotonic() < deadline - 0.05:
        for idx, (name, builder) in enumerate(plan):
            now = time.monotonic()
            if now >= deadline:
                break
            if idx not in cache:
                try:
                    cache[idx] = builder()
                except Exception:
                    cache[idx] = None
                states[idx] = new_state()
            if cache[idx] is None:
                continue
            MT, inv = cache[idx]
            end = min(deadline, now + slice_len)
            try:
                S, c = search(MT, inv, d, end, rng, states[idx])
            except Exception:
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
        slice_len = min(slice_len * 1.5, 6.0)
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================================== cell: d6D5
TARGET = (6, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# Fixed non-abelian families at or just above the threshold 342 (searched first).
PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13)),
    ('Heis(7), order 343', lambda: group_heis(7)),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5)),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18)),
]

# Metacyclic groups of orders 343..372 first (beat the record), then order 342 as a safety net.
for _N, _m, _k, _lam in metacyclic_candidates(343, 372, 2, 28):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))
for _N, _m, _k, _lam in metacyclic_candidates(342, 342, 2, 4):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))

# Valid smaller Haar graph (order 330, 660 vertices), checked at run time; used only when no plan entry succeeds.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit, PLAN, FALLBACK)
