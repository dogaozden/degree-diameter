"""Bold attempt for d=10, D=5: lifts of a 2+2-vertex base multigraph over non-abelian groups.

Parent approach (kept only as fallback): Haar graph on a group G, 2|G| vertices.
New approach: base bipartite multigraph with 2 A-vertices and 2 B-vertices, each of degree d.
Dart (i, j, s) joins (g, A_i) to (s*g, B_j) for all g in G. The graph has 4|G| vertices, is bipartite
and d-regular. Right multiplication by G is an automorphism, so every base vertex's BFS covers its
whole class. Diameter <= 5 therefore reduces to 4 BFS runs (one per base vertex, from the identity).
The annealer minimises the number of unreached pairs over the voltages. Every result is checked
with lib.is_valid. The parent's valid Haar graph (3582 vertices) is the fallback. All other
(d, D) cases return the trivial valid graph immediately.
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
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """GF(q) x| C_k: maps t -> a*t + b, a in the subgroup of order k of GF(q)^*."""
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


# ------------------------------------------------------------------------------ Haar fallback (parent)

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    # K_{d,d}: diameter 2, degree d, bipartite.
    return lib.haar_graph(d, range(d))


def fallback_graph(d, D):
    """The parent's valid Haar graph (order 1791, 3582 vertices), or None if it fails the check."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return None


# ----------------------------------------------------------------------- bold: 2+2 base lifts

def base_blocks(d, a):
    """Dart layout for the 2+2 base with multiplicity matrix [[a, d-a], [d-a, a]]."""
    c = [[a, d - a], [d - a, a]]
    DI, DJ = [], []
    for i in range(2):
        for j in range(2):
            for _ in range(c[i][j]):
                DI.append(i)
                DJ.append(j)
    DI = np.array(DI, dtype=np.int64)
    DJ = np.array(DJ, dtype=np.int64)
    slotA = np.zeros(len(DI), dtype=np.int64)
    slotB = np.zeros(len(DI), dtype=np.int64)
    cntA, cntB = [0, 0], [0, 0]
    for t in range(len(DI)):
        slotA[t] = cntA[DI[t]]
        cntA[DI[t]] += 1
        slotB[t] = cntB[DJ[t]]
        cntB[DJ[t]] += 1
    return DI, DJ, slotA, slotB


class Bold:
    """Lift of the 2+2 base over a group table. A_i vertex (g) is i*N+g, B_j vertex (h) is 2N+j*N+h."""

    def __init__(self, MT, inv, d, a):
        self.MT, self.inv = MT, inv
        self.N = MT.shape[0]
        self.d = d
        self.DI, self.DJ, self.slotA, self.slotB = base_blocks(d, a)
        self.V = 4 * self.N
        self.Boff = 2 * self.N
        self.gs = np.arange(self.N, dtype=np.int64)
        self.srcs = [0, self.N, 2 * self.N, 3 * self.N]

    def nbr(self, DS):
        N, MT, inv = self.N, self.MT, self.inv
        nb = np.empty((self.V, self.d), dtype=np.int64)
        for t in range(len(DS)):
            i, j, s = int(self.DI[t]), int(self.DJ[t]), int(DS[t])
            nb[i * N + self.gs, self.slotA[t]] = self.Boff + j * N + MT[s].astype(np.int64)
            nb[self.Boff + j * N + self.gs, self.slotB[t]] = i * N + MT[int(inv[s])].astype(np.int64)
        return nb

    def cost(self, DS):
        """Number of (source, target) pairs at distance > 5 over the four base-vertex sources."""
        nb = self.nbr(DS)
        total = 0
        for src in self.srcs:
            vis = np.zeros(self.V, dtype=bool)
            vis[src] = True
            front = np.array([src], dtype=np.int64)
            for _ in range(5):
                cand = nb[front].ravel()
                cand = cand[~vis[cand]]
                if cand.size == 0:
                    break
                cand = np.unique(cand)
                vis[cand] = True
                front = cand
            total += self.V - int(vis.sum())
        return total

    def edges(self, DS):
        N, MT = self.N, self.MT
        out = []
        for t in range(len(DS)):
            i, j, s = int(self.DI[t]), int(self.DJ[t]), int(DS[t])
            a = i * N + self.gs
            b = self.Boff + j * N + MT[s].astype(np.int64)
            out.extend(zip(a.tolist(), b.tolist()))
        return self.V, out


def anneal(B, deadline, rng):
    """Anneal the darts to zero cost. Returns the dart voltage array, or None if none found in time."""
    E = len(B.DI)
    N = B.N
    while time.monotonic() < deadline:
        DS = np.zeros(E, dtype=np.int64)
        for t in range(E):
            blk = np.flatnonzero((B.DI == B.DI[t]) & (B.DJ == B.DJ[t]))
            while True:
                s = int(rng.integers(N))
                if not np.any(DS[blk[blk < t]] == s):
                    DS[t] = s
                    break
        cur = B.cost(DS)
        stall = 0
        T = 2.0
        while time.monotonic() < deadline:
            if cur == 0:
                return DS
            t = int(rng.integers(E))
            blk = np.flatnonzero((B.DI == B.DI[t]) & (B.DJ == B.DJ[t]))
            s = int(rng.integers(N))
            if np.any(DS[blk] == s):
                continue
            old = DS[t]
            DS[t] = s
            c = B.cost(DS)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                stall = 0 if delta < 0 else stall + 1
            else:
                DS[t] = old
                stall += 1
            if stall > 3000:
                break
    return None


def group_list():
    """Candidate groups of order about 900-1100, as (order, builder) pairs, best first."""
    cands = [
        (1008, lambda: group_times_cyclic(group_sl2(7), 3)),
        (1029, lambda: group_times_cyclic(group_heis(7), 3)),
        (992, lambda: group_agl(32)),
        (903, lambda: group_agl(43, 21)),
    ]
    for order in range(1001, 1061):
        for k in range(2, 13):
            if order % k:
                continue
            m = order // k
            if m < 3:
                continue
            lam = next((x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1), None)
            if lam is None:
                continue
            cands.append((order, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
            break
    cands.sort(key=lambda c: (c[0] < 1001, c[0] if c[0] >= 1001 else -c[0]))
    return cands


def search_bold(d, D, seed, deadline):
    rng = np.random.default_rng(seed)
    groups = group_list()
    tasks = [(g, a) for g in groups[:4] for a in (d // 2, d // 2 + 1)]
    best = None
    for idx, ((order, builder), a) in enumerate(tasks):
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break
        end = now + remaining / (len(tasks) - idx)
        try:
            MT, inv = builder()
            B = Bold(MT, inv, d, a)
            DS = anneal(B, end, rng)
        except Exception:
            continue
        if DS is None:
            continue
        try:
            n, edges = B.edges(DS)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue
    return best


# ============================================================================== build

TARGET = (10, 5)


def build(d, D, seed, time_limit):
    try:
        if (d, D) != TARGET:
            return trivial(d, D)
        t0 = time.monotonic()
        candidates = []
        fb = fallback_graph(d, D)
        if fb is not None:
            candidates.append(fb)
        bold = search_bold(d, D, seed, t0 + 0.72 * time_limit)
        if bold is not None:
            candidates.append(bold)
        if candidates:
            return max(candidates, key=lambda g: g[0])
        return trivial(d, D)
    except Exception:
        return trivial(d, D)
