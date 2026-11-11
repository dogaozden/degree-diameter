"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a subset of G with |S| = d (the connection set).  The Haar graph has
vertices (g, A) and (g, B) for g in G and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular
with 2|G| vertices.  Right multiplication by any h in G is an automorphism, so every A-vertex looks like (e, A)
and every B-vertex like (e, B).  Its diameter is at most 5 iff
        (S^-1 S)^2 = G   and   (S S^-1)^2 = G
(the left set covers the A side, the right set the B side).  Counting words, |G| <= 1 + d(d-1) + d(d-1)^3,
and in abelian groups many words coincide, so good examples live in non-abelian groups.
COST(S) = (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|) = number of group elements left uncovered; cost 0 = valid.

WHAT THIS FILE DOES.  Builds the group as a multiplication table MT (MT[g, h] = g*h, element 0 = identity),
then runs a local search on S: pick a slot, score K random replacements at once (only the words that involve
the slot are recomputed), accept the best one with a Metropolis rule, restart when stuck.  A start set S0
(near miss from earlier C searches) is tried first.  When cost reaches 0 the graph is built and CHECKED with
lib.is_valid; only a checked graph is ever returned.  If no group reaches cost 0 in the time budget, a
precomputed valid smaller Haar graph (FALLBACK) is returned, so the score is never 0 for a near miss.

CHANGE IN THIS VERSION.  The plan entries are no longer run one after another, each with a fixed time window.
They are now resumable searches that are interleaved in short time slices, and the scheduler always gives the
next slice to the entry with the least time spent relative to its weight.  A near miss that stalls, or one
whose initial scan is slow, can no longer starve the other near misses.  The random-start tier still gets a
smaller share through its weight.  Every candidate is still checked with lib.is_valid.
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
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)   # x^-1 s, s^-1 x
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)   # x s^-1, s x^-1
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


class _Run:
    """A resumable local search over d-subsets of one group.  step(end) runs it until the wall-clock time `end`
    (or until a zero-cost set is found), keeping all state between calls so that it can be interleaved."""

    def __init__(self, MT, inv, d, S0, rng, weight):
        self.MT, self.inv, self.d, self.rng, self.w = MT, inv, d, rng, weight
        self.N = MT.shape[0]
        self.S0 = None if S0 is None else np.array(S0, dtype=np.int32)
        self.best, self.bestc = None, 10 ** 9
        self.S, self.cur, self.since = None, None, 0
        self.started = False
        self.done = False
        self.spent = 0.0

    def _random_set(self):
        return np.concatenate([[0], self.rng.choice(np.arange(1, self.N), self.d - 1, replace=False)]).astype(np.int32)

    def step(self, end, K=24, temp=0.45, patience=4000):
        t_start = time.monotonic()
        MT, inv, d, rng = self.MT, self.inv, self.d, self.rng
        N = self.N
        if not self.started:
            self.started = True
            if self.S0 is not None:
                c0 = cost(MT, inv, self.S0)
                self.best, self.bestc = self.S0.copy(), c0
                if c0 == 0:
                    self.done = True
                    self.spent += time.monotonic() - t_start
                    return
                c1, S1 = one_swap_scan(MT, inv, self.S0, end)
                if S1 is not None and c1 < self.bestc:
                    self.best, self.bestc = S1.copy(), c1
                    self.S = S1.copy()
                    if c1 == 0:
                        self.done = True
                        self.spent += time.monotonic() - t_start
                        return
        while not self.done and time.monotonic() < end:
            if self.S is None:
                if self.S0 is not None and rng.random() < 0.5:
                    self.S = self.S0.copy()
                    for i in rng.choice(d, 2, replace=False):
                        self.S[i] = rng.integers(N)
                    if len(set(self.S.tolist())) < d:
                        self.S = self._random_set()
                else:
                    self.S = self._random_set()
            if self.cur is None:
                self.cur = cost(MT, inv, self.S)
                self.since = 0
                if self.cur < self.bestc:
                    self.best, self.bestc = self.S.copy(), self.cur
                if self.cur == 0:
                    self.done = True
                    break
            i = int(rng.integers(d))
            X = rng.integers(0, N, size=K).astype(np.int32)
            X = X[~np.isin(X, np.delete(self.S, i))]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, self.S, i, X)
            j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
            delta = int(cs[j]) - self.cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                self.S[i] = X[j]
                self.cur = int(cs[j])
                if self.cur < self.bestc:
                    self.best, self.bestc, self.since = self.S.copy(), self.cur, 0
                    if self.cur == 0:
                        self.done = True
                        break
                elif delta < 0:
                    self.since = 0
            self.since += 1
            if self.since > patience:
                self.S, self.cur = None, None
        self.spent += time.monotonic() - t_start


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
    """plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph.
    The plan entries are interleaved in short slices; the next slice goes to the entry with the least
    time spent per unit of weight, so no single group can starve the others."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)
    active = []
    for name, builder, S0, w in plan:
        try:
            MT, inv = builder()
            active.append(_Run(MT, inv, d, S0, rng, w))
        except Exception:
            continue
    SLICE = 2.0
    while active and time.monotonic() < deadline_all:
        r = min(active, key=lambda x: x.spent / x.w)
        now = time.monotonic()
        end = min(deadline_all, now + SLICE)
        try:
            r.step(end)
        except Exception:
            active.remove(r)
            continue
        if r.done:
            active.remove(r)
            try:
                g = checked(r.MT, r.best, d, D)
            except Exception:
                g = None
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


# ======================================================================================== cell: d6D5
# Near-miss reconstruction: the 2-short Haar graphs of orders 351 and 355 (metacyclic) and a 4-short one of order 360 (SL(2,5) x Z_3), scan of all single swaps, then annealing from the near miss with perturbed restarts.
# Interleaved: near misses get the bulk of the weight; random-start searches over metacyclic groups of orders 331..342 get a smaller share.
TARGET = (6, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# (name, group builder, start set S0 or None, weight).  S0 = element indices of the group table.
PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 6),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 6),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 4),
]


def _extra_plan():
    """Random-start tier: metacyclic groups of order 331..342 not already used above."""
    used = {(117, 3, 16), (71, 5, 5)}
    entries = []
    for m, k, lam in meta_candidates(330, 342, used, 6):
        entries.append((f'meta {m}/{k}/{lam} random', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1))
    return entries


# Valid smaller Haar graph, checked at run time; used only when no plan entry reaches cost 0.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    plan = PLAN + _extra_plan()
    return run(d, D, seed, time_limit, plan, FALLBACK)
