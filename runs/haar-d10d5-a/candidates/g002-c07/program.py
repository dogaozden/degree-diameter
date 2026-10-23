"""Bold variant for d=10, D=5: voltage lifts of small bipartite base graphs over metacyclic groups.

A base graph with p A-vertices and p B-vertices is a union of 10 permutation matchings sigma_s, with a
voltage g[a][s] in a group G of order N on each dart (a -> sigma_s(a)).  The lift has 2pN vertices
(a, x) and (B-vertex b, y), with (a, x) ~ (sigma_s(a), x*g[a][s]).  It is bipartite and 10-regular.
Left multiplication by G is an automorphism, so the diameter is at most 5 iff, for each of the 2p base
vertices r, the ball of radius 5 around (r, e) covers all vertices.  This gives a cheap cost (uncovered
vertices summed over the 2p representatives), which is annealed over the voltages.  Any found lift is
checked with lib.is_valid.  If no lift is found in time, the parent's valid Haar graph of order 3582 is
returned.  Other (d, D) cases get the small always-valid graphs.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
DEG = 10
DIAM = 5
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


# ----------------------------------------------------------------------------------------- groups

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


def _metacyclic_options(N):
    """All (m, k, lam) with m*k = N, k >= 2, m >= 3, lam^k = 1 mod m, gcd(lam, m) = 1, lam >= 2."""
    out = []
    for m in range(3, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
    return out


# ------------------------------------------------------------------------------ voltage lifts

def _lift_nbrs(MT, inv, p, sig, sinv, Gv):
    """Neighbour table (2pN, DEG).  A-vertex a*N+x has neighbour (p+sig[s][a])*N + x*Gv[a,s] for each slot s.
    B-vertex (p+b)*N+y has neighbour sinv[s][b]*N + y*Gv[a,s]^-1, with a = sinv[s][b]."""
    N = MT.shape[0]
    x = np.arange(N)
    nbr = np.empty((2 * p * N, DEG), dtype=np.int64)
    for s in range(DEG):
        g = Gv[:, s]
        A_vals = (p + sig[s])[:, None] * N + MT[x[None, :], g[:, None]]
        nbr[:p * N, s] = A_vals.reshape(-1)
        a_of_b = sinv[s]
        gb = inv[Gv[a_of_b, s]]
        B_vals = a_of_b[:, None] * N + MT[x[None, :], gb[:, None]]
        nbr[p * N:, s] = B_vals.reshape(-1)
    return nbr


def _uncovered(nbr, sources):
    """Sum over sources of the number of vertices at distance > DIAM from that source."""
    n = nbr.shape[0]
    total = 0
    for s0 in sources:
        seen = np.zeros(n, dtype=bool)
        seen[s0] = True
        front = np.array([s0], dtype=np.int64)
        for _ in range(DIAM):
            nxt = np.zeros(n, dtype=bool)
            nxt[nbr[front].ravel()] = True
            nxt &= ~seen
            front = np.flatnonzero(nxt)
            if front.size == 0:
                break
            seen |= nxt
        total += n - int(seen.sum())
    return total


def _anneal_lift(p, N, MT, inv, rng, deadline, patience=1500, T=0.8):
    """Anneal voltages for a random 10-regular p+p base.  Returns (sig, Gv) with cost 0, or None."""
    sig = np.array([rng.permutation(p) for _ in range(DEG)], dtype=np.int64)  # sig[s][a]
    sinv = np.argsort(sig, axis=1)
    Gv = np.zeros((p, DEG), dtype=np.int64)
    for a in range(p):
        for s in range(DEG):
            while True:
                g = int(rng.integers(N))
                if all(not (sig[s2, a] == sig[s, a] and Gv[a, s2] == g) for s2 in range(s)):
                    break
            Gv[a, s] = g
    sources = [a * N for a in range(p)] + [(p + b) * N for b in range(p)]
    cur = _uncovered(_lift_nbrs(MT, inv, p, sig, sinv, Gv), sources)
    best, since = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        a = int(rng.integers(p))
        s = int(rng.integers(DEG))
        g = int(rng.integers(N))
        if g == Gv[a, s]:
            continue
        if any(s2 != s and sig[s2, a] == sig[s, a] and Gv[a, s2] == g for s2 in range(DEG)):
            continue
        old = Gv[a, s]
        Gv[a, s] = g
        c = _uncovered(_lift_nbrs(MT, inv, p, sig, sinv, Gv), sources)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if cur < best:
                best, since = cur, 0
        else:
            Gv[a, s] = old
        since += 1
        if since > patience:
            return None
    return (sig, Gv) if cur == 0 else None


def _edges_from(nbr, pN):
    """Edge list from the A-side rows of the neighbour table."""
    src = np.repeat(np.arange(pN, dtype=np.int64), DEG)
    dst = nbr[:pN].ravel()
    return list(zip(src.tolist(), dst.tolist()))


def _search_lift(d, D, rng, deadline):
    """Random restarts over (p, group, base, voltages) until a checked lift of order > 4000 is found."""
    ps = [2, 2, 3, 3, 4, 5]
    while time.monotonic() < deadline:
        p = ps[int(rng.integers(len(ps)))]
        lo = 4001 // (2 * p) + 1          # smallest N with 2pN > 4000
        N = lo + int(rng.integers(0, 12))
        opts = _metacyclic_options(N)
        if not opts:
            continue
        m, k, lam = opts[int(rng.integers(len(opts)))]
        MT, inv = group_meta(m, k, lam)
        found = _anneal_lift(p, N, MT, inv, rng, deadline)
        if found is None:
            continue
        sig, Gv = found
        nbr = _lift_nbrs(MT, inv, p, sig, np.argsort(sig, axis=1), Gv)
        n = 2 * p * N
        edges = _edges_from(nbr, p * N)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


# ------------------------------------------------------------------------------ fallbacks

def checked_haar(MT, S, d, D):
    """The Haar graph for connection set S (vertices (g,A)=g, (g,B)=N+g), or None if not valid."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    edges = [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------------------------- entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    try:
        res = _search_lift(d, D, rng, deadline)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        MT, inv = group_meta(*FALLBACK_GROUP)
        g = checked_haar(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
