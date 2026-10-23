"""Racing search over non-abelian groups for the d=10, D=5 Haar-graph target (numpy only).

A Haar graph over a group G with connection set S (|S| = d) has 2|G| vertices and diameter
at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  This version adds two ideas to the parent:

1. Symmetry normalisation.  Left-translating S by t^-1 gives an isomorphic Haar graph, so we
   can always pin the identity in slot 0 and search only the other d-1 slots.  Conjugation
   also preserves the cost, so starts are canonicalised the same way.
2. Greedy starts and successive-halving racing.  Each candidate group gets a greedy
   coverage-maximising start, and the candidate groups are annealed in rounds.  Half are
   dropped after each round, so the budget concentrates on the groups whose best cost
   falls fastest.

Only a graph checked with lib.is_valid is returned.  Otherwise a valid smaller Haar graph
(or a trivial valid graph) is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l)."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (identity first) and a vectorised product."""
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
    """SL(2, p), order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q):
    """AGL(1, q) = GF(q) x| GF(q)^*, order q(q-1)."""
    F = lib.GF(q)
    H = list(range(1, q))
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) -> g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def build_group(spec):
    kind = spec[0]
    if kind == 'meta':
        return group_meta(spec[1], spec[2], spec[3])
    if kind == 'sl2':
        return group_times_cyclic(group_sl2(7), 6)
    if kind == 'heis':
        return group_times_cyclic(group_heis(7), 6)
    if kind == 'agl':
        return group_times_cyclic(group_agl(13), 13)
    raise ValueError(kind)


def metacyclic_specs(lo, hi):
    """Specs ('meta', m, k, lam) for Z_m x|_lam Z_k with lo <= m*k <= hi, lam != 1."""
    out = []
    for k in range(2, 11):
        for m in range(2, hi // k + 1):
            n = m * k
            if n < lo or n > hi:
                continue
            lams = [lam for lam in range(2, m) if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1][:2]
            out += [('meta', m, k, lam) for lam in lams]
    return out


# ------------------------------------------------------------------------- cost machinery

def _cover(MT, N, P):
    """Boolean array of elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """Side-0 pair products S_i^-1 S_j and side-1 pair products S_i S_j^-1."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements over both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X."""
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


# ------------------------------------------------------ new: normalisation and greedy starts

def normalize(MT, inv, S):
    """Left-translate S so the identity sits in slot 0 (isomorphic Haar graph, same cost)."""
    T = MT[inv[S[0]], S].astype(np.int64)
    idx = int(np.argmax(T == 0))
    T[0], T[idx] = T[idx], T[0]
    return T


def greedy_start(MT, inv, d, rng, cands=48):
    """Build S = {0, ...} one element at a time, each time adding the candidate with least partial cost."""
    N = MT.shape[0]
    S = [0]
    while len(S) < d:
        pool = [int(x) for x in np.unique(rng.integers(1, N, size=cands)) if int(x) not in S]
        if not pool:
            pool = [x for x in range(1, N) if x not in S][:cands]
        scores = [cost(MT, inv, np.array(S + [x], dtype=np.int64)) + rng.random() * 0.5 for x in pool]
        S.append(pool[int(np.argmin(scores))])
    return np.array(S, dtype=np.int64)


def restart_set(MT, inv, d, rng):
    if rng.random() < 0.5:
        return greedy_start(MT, inv, d, rng)
    S = rng.choice(MT.shape[0], d, replace=False).astype(np.int64)
    return normalize(MT, inv, S)


# ------------------------------------------------------------------------- annealing and race

def make_state(spec, d):
    MT, inv = build_group(spec)
    return {'spec': spec, 'MT': MT, 'inv': inv, 'd': d, 'S': None, 'cur': None,
            'best': 10 ** 9, 'bestS': None, 'since': 0}


def anneal(st, deadline, rng, K=24, temp=0.45, patience=2500):
    """Annealing with the identity pinned in slot 0; restarts after `patience` steps without improvement."""
    MT, inv, d = st['MT'], st['inv'], st['d']
    N = MT.shape[0]
    while st['best'] > 0 and time.monotonic() < deadline:
        if st['S'] is None or st['since'] > patience:
            S = restart_set(MT, inv, d, rng)
            c = cost(MT, inv, S)
            st.update(S=S, cur=c, since=0)
            if c < st['best']:
                st.update(best=c, bestS=S.copy())
            continue
        S = st['S']
        st['since'] += 1
        i = int(rng.integers(1, d))
        X = rng.integers(0, N, size=K).astype(np.int64)
        X = X[~np.isin(X, np.delete(S, i))]
        if X.size == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - st['cur']
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            st['cur'] = int(cs[j])
            if st['cur'] < st['best']:
                st.update(best=st['cur'], bestS=S.copy(), since=0)


def race(specs, d, deadline, rng, frac=0.35):
    """Successive halving over groups.  Returns a state with cost 0, or None."""
    states = []
    for spec in specs:
        if time.monotonic() > deadline:
            break
        try:
            states.append(make_state(spec, d))
        except Exception:
            continue
    while len(states) > 1 and time.monotonic() < deadline:
        now = time.monotonic()
        round_end = now + (deadline - now) * frac
        share = (round_end - now) / len(states)
        for st in states:
            anneal(st, time.monotonic() + share, rng)
            if st['best'] == 0:
                return st
        states.sort(key=lambda s: s['best'])
        states = states[:max(1, len(states) // 2)]
    if states:
        anneal(states[0], deadline, rng)
        if states[0]['best'] == 0:
            return states[0]
    return None


# --------------------------------------------------------------------------- output graphs

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if lib.is_valid rejects it."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ============================================================================ cell: d10 D5
TARGET = (10, 5)
LO, HI = 2001, 2060          # |G| > 2000 gives 2|G| > 4000 vertices
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]   # valid Haar graph on Z_199 x| Z_9, 3582 vertices


def group_specs(rng, n_meta=5):
    """Three non-abelian specials plus a random sample of metacyclic groups in [LO, HI]."""
    meta = metacyclic_specs(LO, HI)
    order = rng.permutation(len(meta))
    chosen = [('sl2',), ('heis',), ('agl',)] + [meta[i] for i in order[:n_meta]]
    return chosen


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    try:
        st = race(group_specs(rng), d, deadline, rng)
        if st is not None and st['best'] == 0:
            g = checked(st['MT'], st['bestS'], d, D)
            if g is not None:
                return g
    except Exception:
        pass
    try:
        MT, _ = group_meta(199, 9, 180)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_target(d, D, seed, time_limit)
