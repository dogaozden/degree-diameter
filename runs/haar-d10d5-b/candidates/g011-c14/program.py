"""Multi-orbit group lifts for the bipartite degree-diameter problem, d = 10, D = 5 (numpy only).

IDEA.  A Haar graph has one orbit per side.  Here each side has kb orbits: A-vertices (i, x) and B-vertices (j, y),
with x, y in a group G of order N.  A dart (i, j, g) joins (i, x) to (j, x*g).  Left multiplication by any h in G
is an automorphism, so the graph is bipartite, 10-regular, and has 2*kb*N vertices.  Every vertex lies in a fibre
that G permutes transitively, so the diameter is at most 5 iff each of the 2*kb fibre identities reaches every
vertex within 5 steps.  That needs only 2*kb BFS runs per evaluation.  Dart voltages are annealed until that count
is zero.  Orders with 2*kb*N > 4000 are tried (kb = 3, 4, 2), preferring non-abelian semidirect products.
Any result is checked with lib.is_valid.  If nothing succeeds, the verified Haar fallback (3582 vertices) is returned.
"""
import math
import time

import numpy as np

import lib

DEG = 10
DIAM = 5
TARGET = (10, 5)
TEMP = 2.0
PATIENCE = 800


# ----------------------------------------------------------------------------- group tables

def semidirect_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Identity is 0."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 128):
        hi = min(N, lo + 128)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def candidate_groups(N):
    """Semidirect products of order N: a non-abelian one first (if any), then the cyclic group."""
    out = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
                break
    out.append((N, 1, 1))
    return out


def configs():
    """(kb, N, (m, k, r)) with 2*kb*N > 4000.  Non-abelian groups are tried first."""
    plan = []
    for kb, lo in ((3, 667), (4, 501), (2, 1001)):
        for N in range(lo, lo + 4):
            plan.append((kb, N, candidate_groups(N)[0]))
    plan.sort(key=lambda c: c[2][2] == 1)  # stable: r == 1 (cyclic) goes last
    return plan


def multiplicity(kb):
    """kb x kb dart-multiplicity matrix with row and column sums DEG (cyclic pattern)."""
    q, r = divmod(DEG, kb)
    pat = [q + 1] * r + [q] * (kb - r)
    return [[pat[(j - i) % kb] for j in range(kb)] for i in range(kb)]


# ------------------------------------------------------------------------------ graph and cost

def build_nbr(kb, N, MT, inv, darts):
    """Neighbour array.  A-vertex (i, x) is i*N + x; B-vertex (j, y) is (kb + j)*N + y."""
    V = 2 * kb * N
    nbr = np.empty((V, DEG), dtype=np.int64)
    ca = [0] * kb
    cb = [0] * kb
    x = np.arange(N)
    for i, j, g in darts:
        a0 = i * N
        nbr[a0:a0 + N, ca[i]] = (kb + j) * N + MT[x, g]
        ca[i] += 1
        b0 = (kb + j) * N
        nbr[b0:b0 + N, cb[j]] = i * N + MT[x, inv[g]]
        cb[j] += 1
    return nbr


def cost(kb, N, nbr):
    """Number of (fibre identity, vertex) pairs at distance more than DIAM, summed over all 2*kb fibres."""
    V = nbr.shape[0]
    total = 0
    for src in range(2 * kb):
        reached = np.zeros(V, dtype=bool)
        s = src * N
        reached[s] = True
        frontier = np.array([s], dtype=np.int64)
        for _ in range(DIAM):
            nxt = nbr[frontier].ravel()
            nxt = nxt[~reached[nxt]]
            if nxt.size == 0:
                break
            reached[nxt] = True
            frontier = np.unique(nxt)
        total += V - int(np.count_nonzero(reached))
    return total


# ------------------------------------------------------------------------------------ search

def search(kb, N, MT, inv, rng, deadline):
    """Anneal voltages until cost 0 or the deadline.  Returns the dart list or None."""
    M = multiplicity(kb)
    slots = []
    for i in range(kb):
        for j in range(kb):
            slots += [(i, j)] * M[i][j]
    while time.monotonic() < deadline:
        # random start with distinct voltages inside each (i, j) block
        g = []
        used = {}
        for key in slots:
            s = used.setdefault(key, set())
            x = int(rng.integers(N))
            while x in s:
                x = int(rng.integers(N))
            s.add(x)
            g.append(x)
        darts = [(i, j, g[t]) for t, (i, j) in enumerate(slots)]
        cur = cost(kb, N, build_nbr(kb, N, MT, inv, darts))
        stall = 0
        while cur > 0 and stall < PATIENCE and time.monotonic() < deadline:
            t = int(rng.integers(len(slots)))
            key = slots[t]
            x = int(rng.integers(N))
            if x in used[key]:
                continue
            old = g[t]
            g[t] = x
            darts = [(i, j, g[q]) for q, (i, j) in enumerate(slots)]
            c = cost(kb, N, build_nbr(kb, N, MT, inv, darts))
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                used[key].discard(old)
                used[key].add(x)
                cur = c
                stall = stall + 1 if delta >= 0 else 0
            else:
                g[t] = old
                stall += 1
        if cur == 0:
            return [(i, j, g[t]) for t, (i, j) in enumerate(slots)]
    return None


def multi_orbit(time_limit, seed):
    """Try the configurations in order; return a checked (n, edges) or None."""
    t0 = time.monotonic()
    end = t0 + min(0.85 * time_limit, time_limit - 6.0)
    rng = np.random.default_rng(seed)
    plan = configs()
    for idx, (kb, N, (m, k, r)) in enumerate(plan):
        now = time.monotonic()
        remaining = end - now
        if remaining < 3.0:
            break
        dl = now + remaining / min(len(plan) - idx, 4)
        MT, inv = semidirect_table(m, k, r)
        darts = search(kb, N, MT, inv, rng, dl)
        if darts is None:
            continue
        nbr = build_nbr(kb, N, MT, inv, darts)
        V = nbr.shape[0]
        edges = []
        for a, row in enumerate(nbr[:kb * N].tolist()):
            for b in row:
                edges.append((a, b))
        if lib.is_valid(V, edges, DEG, DIAM):
            return V, edges
    return None


# -------------------------------------------------------------------- Haar fallback and trivial

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = multi_orbit(time_limit, seed)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        MT, _ = semidirect_table(199, 9, 180)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
