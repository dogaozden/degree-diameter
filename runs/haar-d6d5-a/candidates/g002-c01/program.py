"""Degree-6, diameter-5 target: combined voltage-lift search over small bipartite base graphs and non-abelian groups.

Two base families are searched together. Every base vertex has degree 6 in both:
  K : K_{p,p} with r = 6/p parallel darts per pair, p in {1, 2, 3, 6}.
  M : the 2x2 base [[A, 6-A], [6-A, A]] with A random in 1..5 (4 base vertices).
Groups: metacyclic Z_a x|_lam Z_k (cyclic when k = 1) and Heisenberg mod p for order p^3.

A lift over G with dart (u, v, g) joins (u, x) to (v, x*g). Left multiplication is an automorphism, so the diameter
is at most 5 iff each base vertex's identity sheet reaches every vertex within 5 steps. The cost counts uncovered
(vertex, source) pairs, computed by vectorised boolean propagation over all sources at once.
Every candidate is rebuilt explicitly and checked with lib.is_valid. A checked Haar graph of order 660 (or a
small always-valid graph) is the fallback.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
RECORD = 684
SLICE = 1.5          # seconds per annealing attempt
PATIENCE = 3000      # moves without improvement before a restart inside an attempt
TEMP = 0.8           # Metropolis temperature in units of uncovered pairs
RADIUS = 5           # diameter target
FALLBACK_S = [0, 179, 116, 180, 47, 306]
FALLBACK_SPEC = (33, 10, 26)


# ------------------------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def metacyclic_table(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) coded as a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("bad semidirect parameters")
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def heis_table(p):
    """Heisenberg group mod p, element (a, b, c) coded as a*p^2 + b*p + c, product (a+a', b+b', c+c'+a*b')."""
    N = p ** 3
    g = np.arange(N, dtype=np.int64)
    a, b, c = g // (p * p), (g // p) % p, g % p
    MT = (((a[:, None] + a[None, :]) % p) * (p * p)
          + ((b[:, None] + b[None, :]) % p) * p
          + (c[:, None] + c[None, :] + a[:, None] * b[None, :]) % p)
    return _finish(MT)


def groups_of_order(m):
    """Candidate group specs of order m: all metacyclic Z_a x| Z_k (cyclic included), plus Heisenberg if m = p^3."""
    out = []
    for k in range(1, m + 1):
        if m % k:
            continue
        a = m // k
        if a < 2:
            continue
        for lam in range(1, a):
            if math.gcd(lam, a) == 1 and pow(lam, k, a) == 1 % a:
                out.append(("mc", a, k, lam))
    r = round(m ** (1.0 / 3.0))
    for p in (r - 1, r, r + 1):
        if p >= 2 and p ** 3 == m and lib.is_prime_power(p):
            out.append(("heis", p))
    return out


_cache = {}


def group(spec):
    """(MT, INV) for a group spec, cached with a small size cap."""
    if spec not in _cache:
        if len(_cache) > 60:
            _cache.clear()
        if spec[0] == "mc":
            _cache[spec] = metacyclic_table(spec[1], spec[2], spec[3])
        else:
            _cache[spec] = heis_table(spec[1])
    return _cache[spec]


# ------------------------------------------------------------------------------------------ shapes

def K_darts(p, r):
    """K_{p,p} base with r parallel darts per pair. A-base 0..p-1, B-base p..2p-1."""
    return [(i, p + j) for i in range(p) for j in range(p) for _ in range(r)]


def M_darts(A):
    """2x2 base with multiplicity matrix [[A, 6-A], [6-A, A]]. A-base 0,1; B-base 2,3."""
    return ([(0, 2)] * A + [(0, 3)] * (6 - A) + [(1, 2)] * (6 - A) + [(1, 3)] * A)


# ----------------------------------------------------------------------------------- lift and cost

def lift_nb(MT, INV, nA, darts, V):
    """Neighbour table: row b*m+x lists the 6 neighbours of vertex (base b, group element x)."""
    m = MT.shape[0]
    B = 2 * nA
    nb = np.empty((B * m, 6), dtype=np.int64)
    cnt = [0] * B
    for (u, v), g in zip(darts, V):
        g = int(g)
        nb[u * m:(u + 1) * m, cnt[u]] = v * m + MT[:, g]
        nb[v * m:(v + 1) * m, cnt[v]] = u * m + MT[:, INV[g]]
        cnt[u] += 1
        cnt[v] += 1
    return nb


def uncovered(nb, src):
    """Number of (vertex, source) pairs at distance > RADIUS, over all base identity sheets. Zero means valid."""
    n = nb.shape[0]
    S = len(src)
    R = np.zeros((n, S), dtype=bool)
    R[src, np.arange(S)] = True
    for _ in range(RADIUS):
        R = R | R[nb].any(axis=1)
    return n * S - int(np.count_nonzero(R))


def anneal(MT, INV, nA, darts, rng, deadline):
    """Anneal the dart voltages to cost 0. Returns the voltage array, or None at the deadline."""
    m = MT.shape[0]
    src = np.arange(2 * nA, dtype=np.int64) * m
    nd = len(darts)
    V = rng.integers(0, m, size=nd)
    cur = uncovered(lift_nb(MT, INV, nA, darts, V), src)
    stall = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        t = int(rng.integers(nd))
        old = int(V[t])
        V[t] = int(rng.integers(m))
        c = uncovered(lift_nb(MT, INV, nA, darts, V), src)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            stall = 0 if c < cur else stall + 1
            cur = c
        else:
            V[t] = old
            stall += 1
        if stall > PATIENCE:
            V = rng.integers(0, m, size=nd)
            cur = uncovered(lift_nb(MT, INV, nA, darts, V), src)
            stall = 0
    return V


def lift_edges(MT, nA, darts, V):
    """Explicit simple edge list of the lift; vertex (base b, x) has id b*m + x."""
    m = MT.shape[0]
    x = np.arange(m, dtype=np.int64)
    edges = set()
    for (u, v), g in zip(darts, V):
        a = (u * m + x).tolist()
        b = (v * m + MT[:, int(g)]).tolist()
        for p_, q_ in zip(a, b):
            edges.add((p_, q_) if p_ < q_ else (q_, p_))
    return 2 * nA * m, sorted(edges)


# ---------------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def small_graph(d, D):
    """Small always-valid graph for any other (d, D), checked with lib.is_valid."""
    cands = []
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            cands.append(lib.projective_plane_incidence(d - 1))
    except Exception:
        pass
    try:
        cands.append(lib.haar_graph(d, range(d)))
    except Exception:
        pass
    cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for n, edges in cands:
        try:
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    return 1, []


def fallback_graph(d, D):
    """Checked Haar graph of order 660 (group Z_33 x| Z_10), or a small valid graph."""
    try:
        MT, _ = metacyclic_table(*FALLBACK_SPEC)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return small_graph(d, D)


# -------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return small_graph(d, D)

    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.78 * time_limit, time_limit - 10.0))
    rng = np.random.default_rng(seed)

    best = fallback_graph(d, D)
    best_n = best[0]

    # Shapes: ("K", p, r) for K_{p,p} with r parallel darts, and ("M",) for the 2x2 multiplicity base.
    shapes = [("K", p, 6 // p) for p in (1, 2, 3, 6)] + [("M",)]
    jobs = []
    for sh in shapes:
        nA = 2 if sh[0] == "M" else sh[1]
        Btot = 2 * nA
        m_lo = RECORD // Btot + 1          # Btot * m > RECORD
        for m in range(m_lo, m_lo + 4):
            for spec in groups_of_order(m):
                jobs.append((Btot * m, sh, m, spec))
    if not jobs:
        return best

    order = rng.permutation(len(jobs))
    jobs = [jobs[i] for i in order]
    jobs.sort(key=lambda j: j[0])          # stable: random order within each vertex count
    pool_size = min(len(jobs), 60)

    while True:
        if time.monotonic() >= deadline:
            break
        cand = [j for j in jobs[:pool_size] if j[0] > best_n]
        if not cand:
            cand = [j for j in jobs if j[0] > best_n]
            if not cand:
                break
        n_total, sh, m, spec = cand[int(rng.integers(len(cand)))]

        try:
            MT, INV = group(spec)
            if MT.shape[0] != m:
                continue
            if sh[0] == "M":
                nA = 2
                darts = M_darts(int(rng.integers(1, 6)))
            else:
                nA = sh[1]
                darts = K_darts(sh[1], sh[2])
            dl = min(deadline, time.monotonic() + SLICE)
            V = anneal(MT, INV, nA, darts, rng, dl)
        except Exception:
            continue
        if V is None:
            continue

        try:
            n, edges = lift_edges(MT, nA, darts, V)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
        except Exception:
            pass

    return best
