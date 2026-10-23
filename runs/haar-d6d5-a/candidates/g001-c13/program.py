"""Two-orbit voltage lifts over small groups, for the (d, D) = (6, 5) target.

THEORY.  Let G be a finite group, with N = |G| and identity element 0.  Use k A-orbits and k B-orbits, so
the graph has 2kN vertices: A_a(g) and B_b(g) for a, b in 0..k-1 and g in G.  A "dart" (a, b, s) gives the
edges A_a(g) ~ B_b(s*g) for all g.  Each A-orbit has 6 darts and each B-orbit has 6 darts, so the graph is
6-regular and bipartite.  Darts from the same (a, b) pair need distinct s, which keeps the graph simple.

Right multiplication by h in G is an automorphism, so dist((X, g), (Y, x)) = dist((X, 0), (Y, g^-1 x)).
Checking the 2k orbit representatives X_0 with BFS to depth 5 therefore proves diameter <= 5.  COST(S) is
the number of vertices left unreached by those BFS runs, and cost 0 means valid.

With k = 2 and N >= 172, or k = 3 and N >= 115, the order 2kN exceeds the record 684.  Each candidate is
checked with lib.is_valid before it is returned.  If no candidate is found in time, the program returns a
verified smaller Haar graph (660 vertices), or a small always-valid graph as a last resort.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DIAM = 5
DEG = 6

# Count matrices C[a][b] = number of darts from A-orbit a to B-orbit b.  Each row and column sums to DEG.
MATS = {
    2: [
        [[3, 3], [3, 3]],
        [[4, 2], [2, 4]],
        [[2, 4], [4, 2]],
        [[5, 1], [1, 5]],
    ],
    3: [
        [[2, 2, 2], [2, 2, 2], [2, 2, 2]],
        [[3, 2, 1], [2, 1, 3], [1, 3, 2]],
    ],
}
# Group orders chosen so that 2kN > 684.
NRANGE = {2: list(range(172, 186)), 3: list(range(115, 121))}


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with element (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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


def meta_groups(N):
    """All (m, k, lam) with m * k = N giving a metacyclic group Z_m x| Z_k (lam a unit mod m, lam^k = 1 mod m)."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for lam in range(m):
            if math.gcd(lam, m) == 1 and pow(lam, kk, m) == 1 % m:
                out.append((m, kk, lam))
    return out


_GCACHE = {}


def get_group(key):
    """Cached (MT, inv) for a metacyclic key (m, k, lam)."""
    if key not in _GCACHE:
        _GCACHE[key] = group_meta(*key)
    return _GCACHE[key]


# ------------------------------------------------------------------------- lift construction

def slot_layout(C):
    """Dart slots: types[t] = (a, b); cA[t] and cB[t] are the neighbour columns used on each side."""
    k = len(C)
    types = []
    for a in range(k):
        for b in range(k):
            types += [(a, b)] * C[a][b]
    cA, cB = [], []
    ca, cb = [0] * k, [0] * k
    for a, b in types:
        cA.append(ca[a])
        ca[a] += 1
        cB.append(cb[b])
        cb[b] += 1
    return types, cA, cB


def make_nbr(MT, inv, k, N, types, cA, cB, S):
    """Neighbour table (2kN x DEG).  A_a(g) has neighbours B_b(s*g); B_b(h) has neighbours A_a(s^-1 h)."""
    nbr = np.empty((2 * k * N, DEG), dtype=np.int64)
    for t, (a, b) in enumerate(types):
        s = int(S[t])
        nbr[a * N:(a + 1) * N, cA[t]] = (k + b) * N + MT[s].astype(np.int64)
        nbr[(k + b) * N:(k + b + 1) * N, cB[t]] = a * N + MT[int(inv[s])].astype(np.int64)
    return nbr


def cost_of(nbr, k, N):
    """Vertices not reached within DIAM steps, summed over the 2k orbit representatives.  Zero means valid."""
    n = nbr.shape[0]
    srcs = [a * N for a in range(k)] + [(k + b) * N for b in range(k)]
    total = 0
    for src in srcs:
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            cand = nbr[front].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            seen[cand] = True
            front = cand
        total += n - int(np.count_nonzero(seen))
    return total


def edges_of(MT, k, N, types, S):
    """Explicit (n, edges) of the lift for slot values S."""
    edges = []
    for t, (a, b) in enumerate(types):
        row = MT[int(S[t])]
        for g in range(N):
            edges.append((a * N + g, (k + b) * N + int(row[g])))
    return 2 * k * N, edges


# ------------------------------------------------------------------------------- search

def anneal(MT, inv, k, N, types, cA, cB, rng, until, patience=1500, temp=1.5):
    """Simulated annealing over the dart values.  Returns a zero-cost slot vector, or None when time runs out or the search stalls."""
    T = len(types)
    groups = {}
    for t, key in enumerate(types):
        groups.setdefault(key, []).append(t)
    S = np.zeros(T, dtype=np.int64)
    for key, ts in groups.items():
        vals = rng.choice(N, len(ts), replace=False)
        for t, v in zip(ts, vals):
            S[t] = int(v)
    cur = cost_of(make_nbr(MT, inv, k, N, types, cA, cB, S), k, N)
    best = cur
    stall = 0
    while True:
        if cur == 0:
            return S.copy()
        if time.monotonic() >= until or stall > patience:
            return None
        t = int(rng.integers(T))
        key = types[t]
        x = int(rng.integers(N))
        if any(int(S[u]) == x for u in groups[key] if u != t):
            continue
        old = S[t]
        S[t] = x
        c2 = cost_of(make_nbr(MT, inv, k, N, types, cA, cB, S), k, N)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c2
        else:
            S[t] = old
        if cur < best:
            best = cur
            stall = 0
        else:
            stall += 1


# -------------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    """Haar graph of S: A-vertex g is g, B-vertex g is N + g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Small always-valid graph for any (d, D) outside the target."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _safe_trivial(d, D):
    """trivial(d, D) if it passes lib.is_valid, otherwise the single-vertex graph."""
    try:
        g = trivial(d, D)
        if lib.is_valid(g[0], g[1], d, D):
            return g
    except Exception:
        pass
    return (1, [])


# ------------------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _safe_trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + min(0.80 * time_limit, time_limit - 8.0)
    rng = np.random.default_rng(seed)

    while time.monotonic() < deadline - 0.5:
        try:
            k = 2 if rng.random() < 0.6 else 3
            C = MATS[k][int(rng.integers(len(MATS[k])))]
            N = int(NRANGE[k][int(rng.integers(len(NRANGE[k])))])
            glist = meta_groups(N)
            key = glist[int(rng.integers(len(glist)))]
            MT, inv = get_group(key)
            types, cA, cB = slot_layout(C)
            until = min(deadline, time.monotonic() + 6.0)
            S = anneal(MT, inv, k, N, types, cA, cB, rng, until)
            if S is not None:
                n, edges = edges_of(MT, k, N, types, S)
                if lib.is_valid(n, edges, DEG, DIAM):
                    return n, edges
        except Exception:
            continue

    try:
        MT, inv = group_meta(33, 10, 26)
        n, edges = haar_edges(MT, [0, 179, 116, 180, 47, 306])
        if lib.is_valid(n, edges, DEG, DIAM):
            return n, edges
    except Exception:
        pass
    return _safe_trivial(DEG, DIAM)
