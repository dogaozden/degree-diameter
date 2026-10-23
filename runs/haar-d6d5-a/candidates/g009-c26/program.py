"""Bold variant for (d, D) = (6, 5): 2x2-base voltage lifts over non-abelian groups.

Construction: a base multigraph on 2 A-vertices and 2 B-vertices, with 6 darts out of every base vertex.
Each dart carries a voltage in a finite group G of order N, so the lift has 4N vertices and degree 6.
Left multiplication by G is an automorphism that acts transitively on each fibre, so the diameter equals the
maximum eccentricity of the four fibre roots (u, identity). The cost is the number of vertices not reached within
5 steps from those four roots (0 means valid). Simulated annealing searches over the voltages, with a spanning
tree of the base gauged to the identity. Every result is checked with lib.is_valid. The fallback is a checked
Haar graph of order 660, then a trivial valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5
PATIENCE = 3000
TEMP = 2.0


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) coded as a*k + j, product (a, j)(b, l) = (a + lam^j b, j + l)."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def setup(a):
    """Base multigraph: multiplicities (0,0)=a, (0,1)=(1,0)=6-a, (1,1)=a. Returns darts, slots, tree indices."""
    mult = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
    darts = []
    for uv in ((0, 0), (0, 1), (1, 0), (1, 1)):
        darts += [uv] * mult[uv]
    sA, sB = [], []
    cA, cB = [0, 0], [0, 0]
    for u, v in darts:
        sA.append(cA[u])
        cA[u] += 1
        sB.append(cB[v])
        cB[v] += 1
    # First darts of (0,0), (0,1), (1,1) form a spanning tree and are gauged to the identity.
    return darts, sA, sB, [0, a, 2 * DEG - a]


def neighbors(MT, inv, N, st, volt):
    """Neighbour array (4N x DEG). A fibres are vertices 0..2N-1 (A0 at 0, A1 at N), B fibres 2N..4N-1."""
    darts, sA, sB, _ = st
    xs = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, DEG), dtype=np.int64)
    for k, (u, v) in enumerate(darts):
        g = int(volt[k])
        nbr[u * N + xs, sA[k]] = (2 + v) * N + MT[:, g]
        nbr[(2 + v) * N + xs, sB[k]] = u * N + MT[xs, inv[g]]
    return nbr


def cost(nbr, N):
    """Total number of (root, vertex) pairs at distance > DIAM, over the four fibre roots."""
    n = 4 * N
    total = 0
    for s in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(DIAM):
            nx = nbr[fr].ravel()
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            nx = np.unique(nx)
            seen[nx] = True
            fr = nx
        total += n - int(seen.sum())
    return total


def anneal(MT, inv, N, rng, deadline):
    """Annealing over voltages with restarts. Returns (best cost, a, voltages)."""
    best = (10 ** 9, None, None)
    states = {a: setup(a) for a in (2, 3, 4)}
    while time.monotonic() < deadline:
        a = int(rng.choice((2, 3, 4)))
        st = states[a]
        fixed = set(st[3])
        free = [k for k in range(2 * DEG) if k not in fixed]
        volt = rng.integers(0, N, size=2 * DEG).astype(np.int64)
        for k in fixed:
            volt[k] = 0
        cur = cost(neighbors(MT, inv, N, st, volt), N)
        if cur < best[0]:
            best = (cur, a, volt.copy())
        since = 0
        while cur > 0 and since < PATIENCE and time.monotonic() < deadline:
            k = free[int(rng.integers(len(free)))]
            old = int(volt[k])
            volt[k] = int(rng.integers(N))
            nc = cost(neighbors(MT, inv, N, st, volt), N)
            delta = nc - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                cur = nc
                since = 0 if delta < 0 else since + 1
                if cur < best[0]:
                    best = (cur, a, volt.copy())
            else:
                volt[k] = old
                since += 1
        if best[0] == 0:
            break
    return best


def make_graph(MT, inv, N, a, volt):
    st = setup(a)
    nbr = neighbors(MT, inv, N, st, volt)
    edges = set()
    for x in range(2 * N):
        for b in nbr[x].tolist():
            edges.add((x, b))
    return 4 * N, sorted(edges)


def haar_checked(MT, S, d, D):
    """Haar graph of a group table with connection set S, or None if it is not valid."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def lift_candidates(lo, hi, cap):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [lam for lam in range(2, m)
                    if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m]
            for lam in lams[:2]:
                out.append((N, m, k, lam))
    return out[:cap]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline_all = t0 + 0.78 * time_limit
    rng = np.random.default_rng(seed)
    cands = lift_candidates(172, 240, 80) + lift_candidates(171, 171, 4)
    for idx, (N, m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            c, a, volt = anneal(MT, inv, N, rng, end)
            if c == 0:
                n, edges = make_graph(MT, inv, N, a, volt)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        except Exception:
            continue
    try:
        MT, _ = group_meta(33, 10, 26)
        g = haar_checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
