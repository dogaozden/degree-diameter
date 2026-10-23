"""Two-class voltage lifts over non-abelian groups for the bipartite degree-diameter problem (numpy only).

Construction (new for this version): take 2p base classes (p on each side) and a base multigraph in which
every base vertex has degree d.  Each base dart (A_i, B_j, s) with voltage s in a group G gives the edges
(A_i, x) ~ (B_j, x*s) for all x in G.  The result has 2*p*|G| vertices, is bipartite and d-regular.

Lifts commute with left multiplication, so every class is vertex-transitive.  Therefore the diameter is at
most D iff, from each of the 2p class representatives (class, identity), every vertex is reached within D
steps.  This gives an exact, fast cost: the number of (representative, class, element) triples not reached.
Simulated annealing over the voltages drives this cost to 0.  Every returned graph is checked with lib.is_valid.
If no lift is found in time, the parent's valid Haar graph (3582 vertices) is returned, and then a small
always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
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


def meta_specs(lo, hi):
    """(m, k, lam) triples for Z_m x|_lam Z_k with lo <= m*k <= hi (up to two lam per pair), plus cyclic groups."""
    out = []
    for k in range(2, 13):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            lams = [lam for lam in range(2, m) if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1]
            if not lams:
                continue
            chosen = sorted({lams[0], lams[-1]})
            for lam in chosen:
                out.append((m, k, lam))
    for N in range(lo, hi + 1):
        out.append((N, 1, 1))
    return out


# ------------------------------------------------------------------------------- base structure

def _connected(M):
    """True if the bipartite support graph of the p x p nonnegative integer matrix M is connected."""
    p = M.shape[0]
    A, B = {0}, set()
    changed = True
    while changed:
        changed = False
        for i in list(A):
            for j in range(p):
                if M[i, j] and j not in B:
                    B.add(j)
                    changed = True
        for j in list(B):
            for i in range(p):
                if M[i, j] and i not in A:
                    A.add(i)
                    changed = True
    return len(A) == p and len(B) == p


def random_base(p, d, rng):
    """Random p x p multiplicity matrix with all row and column sums d and connected support."""
    while True:
        M = np.zeros((p, p), dtype=np.int64)
        for _ in range(d):
            M[np.arange(p), rng.permutation(p)] += 1
        if _connected(M):
            return M


# ----------------------------------------------------------------------------------- cost evaluation

def evaluate(MT, inv, p, darts, D):
    """Number of (representative, class, element) triples NOT within distance D.  Zero iff diameter <= D.

    Representatives are (class r, identity) for each of the 2p classes; lifts are left-invariant, so
    the eccentricity of each representative covers all vertices.
    """
    N = MT.shape[0]
    R = np.zeros((2 * p, 2 * p, N), dtype=bool)
    for r in range(2 * p):
        R[r, r, 0] = True
    moves = []
    for i, j, s in darts:
        # forward: (A_i, g) -> (B_j, g*s); gather index for target h is h*s^-1
        moves.append((i, p + j, MT[:, inv[s]]))
        # backward: (B_j, h) -> (A_i, h*s^-1); gather index for target g is g*s
        moves.append((p + j, i, MT[:, s]))
    for _ in range(D):
        Rn = R.copy()
        for src, dst, G in moves:
            Rn[:, dst, :] |= R[:, src, G]
        R = Rn
    return int(2 * p * 2 * p * N - np.count_nonzero(R))


def anneal(MT, inv, p, d, D, rng, deadline, patience=2500, T=0.7):
    """Simulated annealing over the voltages of one random base.  Returns (darts or None, cost)."""
    N = MT.shape[0]
    M = random_base(p, d, rng)
    darts = []
    for i in range(p):
        for j in range(p):
            c = int(M[i, j])
            if c:
                for s in rng.choice(N, size=c, replace=False):
                    darts.append([i, j, int(s)])
    cur = evaluate(MT, inv, p, darts, D)
    best = cur
    stall = 0
    while cur > 0 and stall < patience and time.monotonic() < deadline:
        k = int(rng.integers(len(darts)))
        i, j, s = darts[k]
        s2 = int(rng.integers(N))
        if s2 == s or any(a == i and b == j and t == s2 for a, b, t in darts):
            stall += 1
            continue
        old = darts[k]
        darts[k] = [i, j, s2]
        c2 = evaluate(MT, inv, p, darts, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            if cur < best:
                best = cur
                stall = 0
            else:
                stall += 1
        else:
            darts[k] = old
            stall += 1
    return (darts if cur == 0 else None), cur


# --------------------------------------------------------------------------------- graph building

def lift_graph(MT, p, darts):
    """Edges of the 2-sided lift: class A_i = ids i*N..i*N+N-1, class B_j = ids (p+j)*N.., (A_i,x) ~ (B_j,x*s)."""
    N = MT.shape[0]
    a = np.arange(N, dtype=np.int64)
    edges = []
    for i, j, s in darts:
        u = i * N + a
        v = (p + j) * N + MT[a, s].astype(np.int64)
        edges.extend(zip(u.tolist(), v.tolist()))
    return 2 * p * N, edges


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== target case

TARGET = (10, 5)
# (p, lo, hi): p A-classes and p B-classes, group order in [lo, hi], so 2*p*|G| > 4000.
CONFIGS = [(2, 1001, 1040), (3, 667, 700)]

# Valid Haar graph from the parent (3582 vertices), used as the fallback.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)

    pools = [(p, meta_specs(lo, hi)) for p, lo, hi in CONFIGS]
    cache_key, MT, inv = None, None, None

    while time.monotonic() < end:
        p, pool = pools[int(rng.integers(len(pools)))]
        if not pool:
            continue
        spec = pool[int(rng.integers(len(pool)))]
        if spec != cache_key:
            m, k, lam = spec
            try:
                MT, inv = group_meta(m, k, lam)
            except Exception:
                continue
            cache_key = spec
        try:
            darts, cost = anneal(MT, inv, p, d, D, rng, end)
        except Exception:
            continue
        if darts is not None:
            try:
                n, edges = lift_graph(MT, p, darts)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    # Fallback: the parent's valid Haar graph, checked at run time.
    try:
        MT, _ = FALLBACK[0]()
        n, edges = haar_edges(MT, FALLBACK[1])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_target(d, D, seed, time_limit)
