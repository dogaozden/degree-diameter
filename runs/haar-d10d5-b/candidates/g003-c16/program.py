"""Multi-orbit voltage lifts for the bipartite degree-diameter problem, d=10, D=5 (numpy only).

NEW CONSTRUCTION (replaces the single-orbit Haar search for the target).
Take a finite group G of order N and a base bipartite multigraph with two A-orbits and two B-orbits.
Vertices are A_i g = i*N + g and B_j g = (2+j)*N + g for i, j in {0, 1}, g in G.  Each dart (i, j, s)
gives edges (A_i g) ~ (B_j s g) for all g.  Let n_ij be the number of darts between orbits i and j,
with row and column sums equal to d.  Darts in one block (i, j) need distinct voltages, so the graph
is simple and d-regular with 4N vertices.

Right multiplication by h is an automorphism that acts regularly on each orbit.  So the diameter is at
most D iff the ball of radius D around each of the four representatives (e in each orbit) covers all 4N
vertices.  That makes the cost a sum of four BFS counts, which is cheap to evaluate with numpy.

Search: simulated annealing over the 2d voltages, with restarts and random block sizes (p, d-p).
A candidate is returned only after lib.is_valid confirms it.

FALLBACKS: the earlier single-orbit valid Haar graph (3582 vertices), and then a tiny always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (10, 5)


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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
    """Table of a group given as an (N, c) integer coordinate array (identity first) and a vectorised product."""
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
    """SL(2, p) for a prime p, order p(p^2-1)."""
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


def meta_picks(lo, hi, want):
    """A few (m, k, lam) with lo <= m*k <= hi giving non-abelian metacyclic groups."""
    out = []
    for k in range(3, 21):
        for m in range(-(-lo // k), hi // k + 1):
            if m < 2 or m * k < lo or m * k > hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
                    break
        if len(out) >= want:
            break
    return out[:want]


def candidates():
    """Groups for the 2+2 orbit lift, ordered so that orders above 4000 vertices come first (N >= 1001)."""
    C = []
    tier1 = [
        ('Heis7xZ3', lambda: group_times_cyclic(group_heis(7), 3), 1029),
        ('SL27xZ3', lambda: group_times_cyclic(group_sl2(7), 3), 1008),
        ('AGL13xZ7', lambda: group_times_cyclic(group_agl(13), 7), 1092),
        ('GF47:C23', lambda: group_agl(47, 23), 1081),
        ('AGL11xZ10', lambda: group_times_cyclic(group_agl(11), 10), 1100),
        ('SL25xZ9', lambda: group_times_cyclic(group_sl2(5), 9), 1080),
    ]
    tier2 = [
        ('AGL16xZ4', lambda: group_times_cyclic(group_agl(16), 4), 960),
        ('SL25xZ8', lambda: group_times_cyclic(group_sl2(5), 8), 960),
        ('Heis5xZ8', lambda: group_times_cyclic(group_heis(5), 8), 1000),
        ('GF32:C31', lambda: group_agl(32), 992),
    ]
    for name, b, N in tier1:
        C.append((name, b, N, 1.0))
    for m, k, lam in meta_picks(1001, 1100, 2):
        C.append((f'Meta{m}x{k}', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), m * k, 1.0))
    for name, b, N in tier2:
        C.append((name, b, N, 0.5))
    for m, k, lam in meta_picks(896, 1000, 2):
        C.append((f'Meta{m}x{k}', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), m * k, 0.5))
    return C


# ------------------------------------------------------------------------- 2+2 orbit lift machinery

def lift_nbr(MT, inv, N, I, J, S, d):
    """Neighbour table (4N, d) of the lift.  Dart t = (I[t], J[t], S[t]) joins A_I g to B_J (S g)."""
    g = np.arange(N, dtype=np.int64)
    us, ws = [], []
    for i, j, s in zip(I.tolist(), J.tolist(), S.tolist()):
        bb = (2 + j) * N
        us.append(i * N + g)
        ws.append(bb + MT[s].astype(np.int64))
        us.append(bb + g)
        ws.append(i * N + MT[inv[s]].astype(np.int64))
    U = np.concatenate(us)
    W = np.concatenate(ws)
    order = np.argsort(U, kind='stable')
    return W[order].reshape(4 * N, d)


def uncovered(nbr, V, srcs, D):
    """Sum over sources of the number of vertices at distance > D from that source."""
    tot = 0
    for s0 in srcs:
        seen = np.zeros(V, dtype=bool)
        seen[s0] = True
        front = np.array([s0], dtype=np.int64)
        for _ in range(D):
            nb = nbr[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            front = nb
        tot += V - int(seen.sum())
    return tot


def search(MT, inv, N, d, D, rng, deadline, patience=1500):
    """Simulated annealing over the 2d darts of a 2+2 orbit lift.  Returns (S, I, J) with cost 0, or None."""
    V = 4 * N
    srcs = [0, N, 2 * N, 3 * N]
    ps_all = [d // 2, d // 2 + 1, d // 2 - 1, d // 2 + 2, d // 2 - 2]
    ps_all = [p for p in ps_all if 1 <= p <= d - 1]

    while time.monotonic() < deadline:
        p = int(rng.choice(ps_all))
        lens = [p, d - p, d - p, p]
        Iv, Jv = [0, 0, 1, 1], [0, 1, 0, 1]
        I = np.repeat(np.array(Iv, dtype=np.int64), lens)
        J = np.repeat(np.array(Jv, dtype=np.int64), lens)
        starts = np.cumsum([0] + lens)[:-1]
        ends = starts + np.array(lens)
        block_idx = np.repeat(np.arange(4), lens)

        S = np.zeros(2 * d, dtype=np.int64)
        for b in range(4):
            S[starts[b]:ends[b]] = rng.choice(N, size=lens[b], replace=False)

        cur = uncovered(lift_nbr(MT, inv, N, I, J, S, d), V, srcs, D)
        if cur == 0:
            return S, I, J
        best, stale = cur, 0
        while time.monotonic() < deadline and stale < patience:
            t = int(rng.integers(2 * d))
            b = int(block_idx[t])
            lo, hi = int(starts[b]), int(ends[b])
            x = int(rng.integers(N))
            if np.any(S[lo:hi] == x):
                continue
            new = S.copy()
            new[t] = x
            c = uncovered(lift_nbr(MT, inv, N, I, J, new, d), V, srcs, D)
            delta = c - cur
            temp = max(0.5, 0.03 * cur)
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                S, cur = new, c
                if cur == 0:
                    return S, I, J
                if cur < best:
                    best, stale = cur, 0
                else:
                    stale += 1
            else:
                stale += 1
    return None


def graph_edges(nbr, N, d):
    """Return (n, edges) from the neighbour table; A vertices are 0..2N-1 and B vertices 2N..4N-1."""
    U = np.repeat(np.arange(2 * N, dtype=np.int64), d)
    W = nbr[:2 * N].ravel()
    return 4 * N, list(zip(U.tolist(), W.tolist()))


# ------------------------------------------------------------------------------ fallbacks

def haar_checked(MT, S, d, D):
    """Plain Haar graph for S, or None if lib.is_valid rejects it."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    edges = []
    for s in S:
        edges.extend((int(a), int(N + b)) for a, b in zip(g.tolist(), MT[s].tolist()))
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------- the program

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8))
    end = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    total_w = sum(c[3] for c in cands)
    for name, builder, N, w in cands:
        now = time.monotonic()
        if now >= end:
            break
        dl = now + (end - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            if MT.shape[0] != N:
                continue
            res = search(MT, inv, N, d, D, rng, dl)
            if res is None:
                continue
            S, I, J = res
            nbr = lift_nbr(MT, inv, N, I, J, S, d)
            n, edges = graph_edges(nbr, N, d)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            continue
    # Safe fallback: the known valid single-orbit Haar graph of order 3582.
    try:
        MT, _ = group_meta(199, 9, 180)
        g = haar_checked(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
