"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S of d elements, the Haar graph has vertices
(g, A), (g, B) and edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and has
diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both
sides; cost 0 means a valid graph.  Any group of order >= 343 with cost 0 beats the record 684 = 2*342.

WHAT IS NEW IN THIS VERSION.
  * Guided moves.  Besides random replacements, a move picks an uncovered element u and sets the new
    slot x so that one new word equals u exactly (x = t*u^-1 when side 0 is repaired, x = u*t when side 1
    is repaired, with t a slot already in S).  Half of the proposals are guided.
  * Round-robin warm-start annealing.  Many groups of orders 343..392 (non-abelian metacyclic
    Z_m x| Z_k and small AGL / Heisenberg products) are searched in turns.  Each group keeps its own
    current set, best set and cost.  The time slice grows geometrically, so cheap groups are tested
    early and long searches continue on the most promising groups.
  * Automatic enumeration of metacyclic groups of a given order range.

Every returned graph is checked with lib.is_valid.  If nothing reaches cost 0, a smaller valid Haar
graph is returned.
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def metacyclic_specs(lo, hi, cap):
    """Up to `cap` non-abelian metacyclic groups Z_m x| Z_k with order m*k in [lo, hi] (first valid lam per (m, k))."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if len(out) >= cap:
                return out
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1), None)
            if lam is None:
                continue
            out.append((f"Z_{m} x| Z_{k} (lam={lam})",
                        lambda m=m, k=k, lam=lam: group_meta(m, k, lam), 1))
    return out


# ------------------------------------------------------------------------------------------- cost model

def _cover(MT, N, P):
    """Boolean array of the elements covered by the pairwise products of the index array P."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements on both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only the words involving slot i are recomputed)."""
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


# ------------------------------------------------------------------------------------ new move generator

def uncovered(MT, inv, S):
    """Uncovered elements of side 0 and side 1 for the current set S."""
    N = MT.shape[0]
    P0, P1 = _pairs(MT, inv, S)
    u0 = np.nonzero(~_cover(MT, N, np.unique(P0)))[0]
    u1 = np.nonzero(~_cover(MT, N, np.unique(P1)))[0]
    return u0, u1


def propose(MT, inv, S, i, rng, K):
    """Candidate values for slot i.  Half are random; half aim one new word at an uncovered element u:
    side 0 uses x = t*u^-1 (so x^-1 t = u); side 1 uses x = u*t (so x t^-1 = u), with t an element of S."""
    N = MT.shape[0]
    if rng.random() < 0.5:
        return rng.integers(0, N, size=K).astype(np.int32)
    rest = np.delete(S, i)
    u0, u1 = uncovered(MT, inv, S)
    side = int(rng.integers(2))
    unc = u0 if side == 0 else u1
    if len(unc) == 0:
        return rng.integers(0, N, size=K).astype(np.int32)
    u = int(unc[rng.integers(len(unc))])
    t = rest[rng.integers(len(rest), size=K)]
    if side == 0:
        X = MT[t, inv[u]]
    else:
        X = MT[u, t]
    return X.astype(np.int32)


def perturb(MT, d, base, rng):
    """A new d-set: a copy of base with two slots randomised (60% of the time when base is given), else random."""
    N = MT.shape[0]
    if base is not None and rng.random() < 0.6:
        S = base.copy()
        for i in rng.choice(d, 2, replace=False):
            S[i] = rng.integers(N)
        if len(set(S.tolist())) == d:
            return S.astype(np.int32)
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def anneal(MT, inv, d, st, deadline, rng, K=24, temp=0.45, patience=3000):
    """Continue the annealing stored in dict st until the deadline or until cost 0 is found."""
    while st['bestc'] > 0 and time.monotonic() < deadline:
        S = st['S']
        i = int(rng.integers(d))
        X = propose(MT, inv, S, i, rng, K)
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
                st['bestc'], st['best'], st['since'] = st['cur'], S.copy(), 0
                continue
        st['since'] += 1
        if st['since'] > patience:
            S2 = perturb(MT, d, st['best'], rng)
            st['S'] = S2
            st['cur'] = cost(MT, inv, S2)
            st['since'] = 0
            if st['cur'] < st['bestc']:
                st['bestc'], st['best'] = st['cur'], S2.copy()


# --------------------------------------------------------------------------------------------- the graph

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


# ------------------------------------------------------------------------------------------ driver

def run(d, D, seed, time_limit, specs, fallback):
    """Round-robin warm-start annealing over the groups in specs (name, builder, weight)."""
    end = time.monotonic() + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    states = [dict(name=nm, builder=bd, w=w, MT=None, inv=None, dead=False,
                   S=None, cur=0, best=None, bestc=10 ** 9, since=0)
              for nm, bd, w in specs]
    slice_s = 0.5
    while time.monotonic() < end:
        active = False
        for st in states:
            if st['dead'] or st['bestc'] == 0:
                continue
            now = time.monotonic()
            if now >= end:
                break
            active = True
            if st['MT'] is None:
                try:
                    MT, inv = st['builder']()
                    S = perturb(MT, d, None, rng)
                    cur = cost(MT, inv, S)
                except Exception:
                    st['dead'] = True
                    continue
                st.update(MT=MT, inv=inv, S=S, cur=cur, best=S.copy(), bestc=cur)
            anneal(st['MT'], st['inv'], d, st, min(end, now + slice_s * st['w']), rng)
            if st['bestc'] == 0:
                g = checked(st['MT'], st['best'], d, D)
                if g is not None:
                    return g
                st['dead'] = True
        slice_s *= 1.5
        if not active:
            break
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def _specs():
    """Non-abelian groups of order just above 342 (2|G| > 684), plus a metacyclic enumeration."""
    specs = [
        ('Heis(3) x Z_13, 351', lambda: group_times_cyclic(group_heis(3), 13), 2),
        ('Heis(7), 343', lambda: group_heis(7), 2),
        ('AGL(1,9) x Z_5, 360', lambda: group_times_cyclic(group_agl(9), 5), 2),
        ('AGL(1,5) x Z_18, 360', lambda: group_times_cyclic(group_agl(5), 18), 2),
        ('Heis(5) x Z_3, 375', lambda: group_times_cyclic(group_heis(5), 3), 1),
        ('AGL(1,7;6) x Z_9, 378', lambda: group_times_cyclic(group_agl(7, 6), 9), 1),
        ('Heis(3) x Z_14, 378', lambda: group_times_cyclic(group_heis(3), 14), 1),
        ('AGL(1,8) x Z_7, 392', lambda: group_times_cyclic(group_agl(8), 7), 1),
        ('AGL(1,11;5) x Z_7, 385', lambda: group_times_cyclic(group_agl(11, 5), 7), 1),
        ('AGL(1,13;6) x Z_5, 390', lambda: group_times_cyclic(group_agl(13, 6), 5), 1),
    ]
    specs += metacyclic_specs(343, 380, 6)
    return specs


TARGET = (6, 5)

# Valid smaller Haar graph (order 330, 660 vertices), used only if no search reaches cost 0.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit, _specs(), FALLBACK)
    except Exception:
        return trivial(d, D)
