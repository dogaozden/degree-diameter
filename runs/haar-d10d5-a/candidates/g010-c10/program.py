"""Lift search for the bipartite degree-diameter problem, d=10, D=5 (numpy only).

Construction: a 2x2 base multigraph with parts A0,A1 | B0,B1 and integer counts c[i][j], where each row and
column sums to d=10. Each base dart (i, j, h) with a group element h gives edges (A_i, g) ~ (B_j, g*h) for all g
in G. Every lift has 4|G| vertices and is 10-regular. Distinct voltages inside each block keep the graph simple.

Left multiplication by any k in G is an automorphism that fixes each class, so the diameter is at most 5 iff
every vertex is within distance 5 of the four identity vertices A0, A1, B0, B1. The cost is the number of
unreached vertices, summed over those four BFS balls. Simulated annealing over the voltages drives the cost to 0.
Only a graph that passes lib.is_valid is returned. Otherwise a valid Haar graph of order 3582 is returned.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
DEG = 10
NLO, NHI = 1001, 1040        # group order N gives 4N > 4000 vertices
CYCLE = 6.0                  # seconds per temperature cycle
T_HOT, T_COLD = 3.0, 0.05


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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


def candidate_groups(lo, hi, rng):
    """All (N, abelian, m, k, lam) with N = m*k in [lo, hi], lam^k = 1 mod m. Non-abelian first within each N."""
    out = []
    for k in range(1, hi + 1):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            for lam in range(1, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    N = m * k
                    if lo <= N <= hi:
                        out.append((N, lam == 1, m, k, lam))
    rng.shuffle(out)
    out.sort(key=lambda t: (t[0], t[1]))
    return out


# ------------------------------------------------------------------------------- lift model

def build_nb(MTT, inv, N, B):
    """Adjacency array (4N x DEG). Vertex A_i(g) = i*N + g, B_j(x) = 2N + j*N + x.
    A_i(g) ~ B_j(g*h) for each dart h in B[i][j]. MTT[h] is column h of the table, so MTT[h][g] = g*h."""
    NB = np.empty((4 * N, DEG), dtype=np.int64)
    for i in (0, 1):
        cols = []
        for j in (0, 1):
            for h in B[i][j]:
                cols.append(2 * N + j * N + MTT[h])
        NB[i * N:(i + 1) * N] = np.stack(cols, axis=1)
    for j in (0, 1):
        cols = []
        for i in (0, 1):
            for h in B[i][j]:
                cols.append(i * N + MTTinv(MTT, inv, h))
        NB[2 * N + j * N: 2 * N + (j + 1) * N] = np.stack(cols, axis=1)
    return NB


def MTTinv(MTT, inv, h):
    """Column of the table at the inverse of h: x -> x*h^-1."""
    return MTT[inv[h]]


def unreached(NB, src, V):
    """Vertices not within distance 5 of src."""
    seen = np.zeros(V, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(5):
        nb = NB[front].ravel()
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        seen[nb] = True
        front = nb
    return V - int(seen.sum())


def anneal(MTT, inv, N, c, rng, deadline):
    """Anneal the 2x2 voltage blocks. Returns B (B[i][j] = voltage array) with cost 0, or None at the deadline."""
    V = 4 * N
    src = [0, N, 2 * N, 3 * N]
    cnt = [[c, DEG - c], [DEG - c, c]]
    B = [[rng.choice(N, cnt[i][j], replace=False).astype(np.int64) for j in (0, 1)] for i in (0, 1)]

    def cost_of():
        NB = build_nb(MTT, inv, N, B)
        return sum(unreached(NB, s, V) for s in src)

    cur = cost_of()
    t_begin = time.monotonic()
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = ((now - t_begin) % CYCLE) / CYCLE
        T = T_HOT * (T_COLD / T_HOT) ** frac
        i, j = int(rng.integers(2)), int(rng.integers(2))
        arr = B[i][j]
        t = int(rng.integers(len(arr)))
        h = int(rng.integers(N))
        if (arr == h).any():
            continue
        old = int(arr[t])
        arr[t] = h
        new = cost_of()
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            arr[t] = old
    return B


def to_graph(MTT, N, B):
    g = np.arange(N, dtype=np.int64)
    parts = []
    for i in (0, 1):
        for j in (0, 1):
            for h in B[i][j]:
                parts.append(np.stack([i * N + g, 2 * N + j * N + MTT[h]], axis=1))
    E = np.vstack(parts)
    return 4 * N, [(int(a), int(b)) for a, b in E]


def lift_search(rng, deadline):
    cands = candidate_groups(NLO, NHI, rng)[:24]
    if not cands:
        return None
    t_start = time.monotonic()
    window = max(1.0, deadline - t_start)
    ci = 0
    while True:
        now = time.monotonic()
        if now >= deadline - 1.0:
            break
        N, _, m, k, lam = cands[ci % len(cands)]
        ci += 1
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        MTT = np.ascontiguousarray(MT.T, dtype=np.int64)
        inv = inv.astype(np.int64)
        c = int(rng.choice([4, 5, 6]))
        budget = min(deadline - now, max(5.0, 0.3 * window))
        B = anneal(MTT, inv, N, c, rng, now + budget)
        if B is None:
            continue
        n, edges = to_graph(MTT, N, B)
        if lib.is_valid(n, edges, DEG, 5):
            return n, edges
    return None


# -------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def checked_haar():
    """Valid smaller Haar graph of order 3582 for d=10, D=5, or None."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, DEG, 5):
            return n, edges
    except Exception:
        pass
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    deadline = t0 + 0.72 * time_limit
    try:
        res = lift_search(rng, deadline)
    except Exception:
        res = None
    if res is not None:
        return res
    fb = checked_haar()
    if fb is not None:
        return fb
    return trivial(d, D)
