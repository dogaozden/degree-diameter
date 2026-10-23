"""Multi-orbit voltage lifts for the bipartite degree-diameter problem at (d, D) = (6, 5).

THEORY.  Let G be a finite group of order N and let r >= 2.  Take r "A-orbits" and r "B-orbits", each a copy of G.
Choose a nonnegative integer r x r matrix M with all row and column sums equal to d = 6.  For every pair (i, j)
pick a set S_ij of M[i][j] distinct group elements.  Vertices are (A_i, x) and (B_j, y).  Edges are
(A_i, x) ~ (B_j, g x) for every g in S_ij.  Each A_i and B_j vertex has degree 6, and the graph is bipartite with
2rN vertices.  The map x -> x h (right multiplication) is an automorphism, so every vertex can be moved to the
identity of its orbit.  Diameter <= 5 therefore holds iff every ball of radius 5 around the 2r identity vertices
(one per orbit) covers the whole graph.  COST = total number of uncovered vertices over those 2r balls, and cost 0
means valid.  Each cost evaluation is a handful of numpy BFS passes, so the search runs fast.

WHY THIS IS NEW.  The previous program used a single Haar orbit per side (r = 1).  Here r = 2, 3 and 4 give
graphs of order 4N, 6N and 8N, so smaller groups (N = 86..200) can reach orders above the record 684.  The
construction is a genuine multi-orbit voltage lift, not a Haar graph.

SAFETY.  A checked Haar graph of order 660 is computed first and kept as the fallback.  Any graph returned is
checked with lib.is_valid.  If nothing better is found, the program returns the largest valid graph it has.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j.  Needs lam^k = 1 mod m."""
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
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (maps t -> a t + b with a in the order-k subgroup of GF(q)^*); default AGL(1, q)."""
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
    """Metacyclic parameters (m, k, lam) with m prime, k | m-1, lo <= m*k <= hi, lam^k = 1 mod m, lam != 1."""
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


# ------------------------------------------------------------------------------ multi-orbit lift

def _rand_M(r, rng):
    """r x r nonnegative integer matrix with all row and column sums DEG, all entries positive if possible."""
    M = np.zeros((r, r), dtype=np.int64)
    for _ in range(200):
        M = np.zeros((r, r), dtype=np.int64)
        for _ in range(DEG):
            M[np.arange(r), rng.permutation(r)] += 1
        if (M > 0).all():
            return M
    return M


def _nbr(MT, inv, r, S):
    """Neighbour table (2rN, DEG).  A_i vertex x is i*N + x; B_j vertex y is r*N + j*N + y.
    Edge (A_i, x) ~ (B_j, g x) for g in S[i][j]."""
    N = MT.shape[0]
    n = 2 * r * N
    nbr = np.empty((n, DEG), dtype=np.int64)
    for i in range(r):
        G, J = [], []
        for j in range(r):
            for g in S[i][j]:
                G.append(int(g))
                J.append(j)
        G = np.array(G, dtype=np.int64)
        J = np.array(J, dtype=np.int64)
        nbr[i * N:(i + 1) * N] = r * N + J[None, :] * N + MT[G].T
    for j in range(r):
        H, I = [], []
        for i in range(r):
            for g in S[i][j]:
                H.append(int(g))
                I.append(i)
        H = np.array(H, dtype=np.int64)
        I = np.array(I, dtype=np.int64)
        nbr[r * N + j * N:r * N + (j + 1) * N] = I[None, :] * N + MT[inv[H]].T
    return nbr


def _cost(nbr, N, r):
    """Uncovered vertices summed over the balls of radius 5 around the identity of each of the 2r orbits."""
    n = nbr.shape[0]
    total = 0
    for o in range(2 * r):
        rep = o * N
        seen = np.zeros(n, dtype=bool)
        seen[rep] = True
        front = np.array([rep], dtype=np.int64)
        for _ in range(5):
            nxt = nbr[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def _graph(r, N, nbr):
    n = 2 * r * N
    us = np.repeat(np.arange(r * N, dtype=np.int64), DEG)
    vs = nbr[:r * N].ravel()
    return n, list(zip(us.tolist(), vs.tolist()))


def _search(MT, inv, r, t_end, rng, temp=1.0, patience=2500):
    """Simulated annealing over the sets S_ij with restarts.  Returns (S, 0) on success, else (None, cost)."""
    N = MT.shape[0]

    def fresh():
        M = _rand_M(r, rng)
        S = [[None] * r for _ in range(r)]
        for i in range(r):
            for j in range(r):
                S[i][j] = rng.choice(N, size=int(M[i, j]), replace=False).astype(np.int64)
        pairs = [(i, j) for i in range(r) for j in range(r) if M[i, j] > 0]
        return S, pairs

    S, pairs = fresh()
    cur = _cost(_nbr(MT, inv, r, S), N, r)
    since = 0
    while time.monotonic() < t_end:
        if cur == 0:
            return S, 0
        i, j = pairs[int(rng.integers(len(pairs)))]
        arr = S[i][j]
        k = int(rng.integers(len(arr)))
        x = int(rng.integers(N))
        if np.any(arr == x):
            continue
        old = int(arr[k])
        arr[k] = x
        c = _cost(_nbr(MT, inv, r, S), N, r)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            if c < cur:
                since = 0
            cur = c
        else:
            arr[k] = old
        since += 1
        if since > patience:
            S, pairs = fresh()
            cur = _cost(_nbr(MT, inv, r, S), N, r)
            since = 0
    return None, cur


def _candidates():
    """(r, order, name, builder) for groups whose r-orbit lift can reach order > 684 (need 2 r N > 684)."""
    lo = {2: 172, 3: 115, 4: 86}
    explicit = [
        (120, 3, 'SL(2,5)', lambda: group_sl2(5)),
        (125, 3, 'Heis(5)', lambda: group_heis(5)),
        (126, 3, 'AGL(1,7)xZ3', lambda: group_times_cyclic(group_agl(7), 3)),
        (120, 3, 'AGL(1,5)xZ6', lambda: group_times_cyclic(group_agl(5), 6)),
        (96, 4, 'SL(2,3)xZ4', lambda: group_times_cyclic(group_sl2(3), 4)),
        (100, 4, 'AGL(1,5)xZ5', lambda: group_times_cyclic(group_agl(5), 5)),
        (108, 4, 'Heis(3)xZ4', lambda: group_times_cyclic(group_heis(3), 4)),
        (110, 4, 'AGL(1,11)', lambda: group_agl(11)),
        (180, 2, 'AGL(1,5)xZ9', lambda: group_times_cyclic(group_agl(5), 9)),
        (189, 2, 'Heis(3)xZ7', lambda: group_times_cyclic(group_heis(3), 7)),
        (192, 2, 'SL(2,3)xZ8', lambda: group_times_cyclic(group_sl2(3), 8)),
        (240, 2, 'AGL(1,16)', lambda: group_agl(16)),
    ]
    out = []
    for order, r, name, b in explicit:
        if order >= lo[r]:
            out.append((r, order, name, b))
    for r in (2, 3, 4):
        cnt = 0
        for m, k, lam in meta_candidates(lo[r], lo[r] + 40, kmin=2, kmax=8):
            out.append((r, m * k, f'meta {m}/{k}/{lam}',
                        (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
            cnt += 1
            if cnt >= 3:
                break
    return out


# ------------------------------------------------------------------------------------ fallback

def _fallback():
    """Valid Haar graph of order 660 (group Z_33 x| Z_10), checked; used if nothing better is found."""
    MT, _ = group_meta(33, 10, 26)
    S = [0, 179, 116, 180, 47, 306]
    N = MT.shape[0]
    edges = [(int(a), int(N + b)) for s in S for a, b in zip(np.arange(N), MT[s])]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, DEG, 5) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.78 * time_limit
    best = None
    try:
        best = _fallback()
    except Exception:
        best = None

    rng = np.random.default_rng(seed)
    cands = _candidates()
    cache = {}
    k = 0
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        floor = best[0] if best is not None else 0
        active = [c for c in cands if 2 * c[0] * c[1] > floor]
        if not active:
            break
        r, order, name, builder = active[k % len(active)]
        k += 1
        t_end = min(deadline, now + 5.0)
        try:
            if name not in cache:
                cache[name] = builder()
            MT, inv = cache[name]
            S, c = _search(MT, inv, r, t_end, rng)
            if S is not None and c == 0:
                N = MT.shape[0]
                nbr = _nbr(MT, inv, r, S)
                n, edges = _graph(r, N, nbr)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
        except Exception:
            continue

    if best is None:
        return trivial(d, D)
    return best[0], best[1]
