"""Haar-graph annealing over larger nonabelian groups for d=6, D=5 (numpy only).

CONSTRUCTION.  Haar graph H(G, S): vertices A_g and B_g for g in G, edges A_g ~ B_{s*g} for s in S, |S| = d.
Right multiplication by h is an automorphism (A_g -> A_{gh}, B_x -> B_{xh}), so each side is vertex-transitive,
and diameter <= 5 iff BFS of radius 5 from A_e and from B_e reaches every vertex. The graph has 2|G| vertices,
so |G| >= 343 beats the record 684.

CHANGE FROM PARENT.  The parent searched bi-Cayley graphs with four orbits (order 4N, N >= 172) and fell back
to a 660-vertex Haar graph. This version switches to a two-orbit Haar graph with fewer free parameters, aimed at
groups of order 343 and up: Heisenberg(7) (exactly 343), Heis(3) x Z_k, Heis(5) x Z_3, and metacyclic
Z_m x| Z_k. Candidates are tried in ascending order of size, with the time budget shared among them.

SAFETY.  The 660-vertex Haar fallback is checked with lib.is_valid before the search starts. Every returned
graph is checked with lib.is_valid. Other (d, D) cases return a checked small graph (projective plane for D=3
when d-1 is a prime power, otherwise K_{d,d}).
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 343          # 2 * 343 = 686 > 684 (record)
STALL = 3000
MAX_CANDIDATES = 12
T_START = 0.5


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
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


# ------------------------------------------------------------------------------- candidate groups

def _candidates():
    """Nonabelian groups of order in [343, 372], as specs sorted by order (at most MAX_CANDIDATES)."""
    out = []
    for NN in range(MIN_N, MIN_N + 30):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((NN, ("meta", m, k, lam)))
                    break
    out.append((343, ("hcyc", 7, 1)))   # Heisenberg mod 7, order 343
    out.append((351, ("hcyc", 3, 13)))  # Heis(3) x Z_13
    out.append((375, ("hcyc", 5, 3)))   # Heis(5) x Z_3
    out.append((378, ("hcyc", 3, 14)))  # Heis(3) x Z_14
    out.sort(key=lambda t: t[0])
    return [spec for _, spec in out[:MAX_CANDIDATES]]


def _make(spec):
    if spec[0] == "meta":
        return group_meta(spec[1], spec[2], spec[3])
    return group_times_cyclic(group_heis(spec[1]), spec[2])


# ------------------------------------------------------------------------------- Haar graph helpers

def _edges(MT, S, N):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    g = np.arange(N).tolist()
    edges = [(a, N + b) for s in S for a, b in zip(g, MT[int(s)].tolist())]
    return 2 * N, edges


def _haar_checked(MT, S, d, D):
    N = MT.shape[0]
    n, edges = _edges(MT, S, N)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def _fallback_660(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked at run time), or None."""
    try:
        MT, _ = group_meta(33, 10, 26)
        return _haar_checked(MT, [0, 179, 116, 180, 47, 306], d, D)
    except Exception:
        return None


def _cost(nb, N):
    """Vertices not reached within DIAM steps from A_e and B_e (0 means valid)."""
    n = 2 * N
    total = 0
    for src in (0, N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nb[fr].ravel()
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            nx = np.unique(nx)
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


def _anneal(MT, inv, N, d, deadline, rng):
    """Anneal a size-d connection set S until the Haar cost is 0; return a checked (n, edges) or None."""
    T = T_START

    def nbr_of(S):
        nb = np.empty((2 * N, d), dtype=np.int64)
        nb[:N] = N + MT[S, :].T          # A_g ~ B_{s g}
        nb[N:] = MT[inv[S], :].T         # B_x ~ A_{s^-1 x}
        return nb

    while time.monotonic() < deadline:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        cur = _cost(nbr_of(S), N)
        stall = 0
        while cur > 0 and stall < STALL and time.monotonic() < deadline:
            pos = int(rng.integers(d))
            x = int(rng.integers(N))
            if x in S:
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(nbr_of(newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            n, edges = _edges(MT, S, N)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# ------------------------------------------------------------------------------- other cases

def _small(d, D):
    """Always-valid small graph for any other (d, D), checked before returning."""
    cands = []
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 16:
            cands.append(lib.projective_plane_incidence(d - 1))
    except Exception:
        pass
    if D >= 2 and d >= 1:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if d >= 1 and D >= 1:
        cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for n, edges in cands:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 1, []


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _small(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 12.0))
    deadline = t0 + budget

    best = _fallback_660(d, D)
    try:
        rng = np.random.default_rng(seed)
        cands = _candidates()
        for idx, spec in enumerate(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            end = now + (deadline - now) / (len(cands) - idx)
            try:
                MT, inv = _make(spec)
                N = MT.shape[0]
                g = _anneal(MT, inv, N, d, end, rng)
            except Exception:
                continue
            if g is not None and (best is None or g[0] > best[0]):
                best = g
    except Exception:
        pass

    if best is None:
        best = _small(d, D)
    return best
