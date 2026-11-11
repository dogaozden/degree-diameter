"""Multi-orbit bipartite lifts for the (d=6, D=5) target (numpy + lib only).

NEW CONSTRUCTION.  The parent searches Haar graphs: one group G, two vertex orbits, 2|G| vertices.  This program
searches a wider family.  Take a metacyclic group G of order N and an a-by-a nonnegative integer matrix M whose rows
and columns each sum to d.  The base multigraph has a A-orbits and a B-orbits, with M[i][j] darts from A_i to B_j.
Vertices are (g, A_i) and (g, B_j), and each dart (i, j, s) gives edges (g, A_i) ~ (g*s, B_j) for all g.  The graph
is bipartite and d-regular on 2*a*N vertices.  Left multiplication by any h in G is an automorphism, so validity
reduces to: from each of the 2a orbit representatives (identity, orbit i), every vertex lies within distance D.
That is a cheap vectorised BFS, and the cost (number of unreached (source, vertex) pairs) drives simulated annealing
over the voltages.  Orders 2*a*N above 660 are targeted, with a=2 (N near 171), a=3 (N near 115) and a=4 (N near 86).

Safety: every candidate result is checked with lib.is_valid.  If nothing valid above the baseline is found, the
parent's valid order-660 Haar graph is returned, and K_{d,d} is the last resort.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)


# ----------------------------------------------------------------------------- groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> index a*k + j, identity index 0.  Needs lam^k = 1 mod m."""
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
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def meta_list(N):
    """Candidate metacyclic parameters (m, k, lam) with m*k = N, non-abelian ones first, cyclic last."""
    out = []
    for k in range(2, 10):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
                break
    out.append((N, 1, 1))
    return out


# ----------------------------------------------------------------------------- lifts

def random_M(a, d, rng):
    """Sum of d random permutation matrices: row and column sums are all d."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = rng.permutation(a)
        for i in range(a):
            M[i][int(p[i])] += 1
    return M


def connected(M, a):
    """True if the bipartite base multigraph on 2a orbit nodes is connected."""
    par = list(range(2 * a))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for i in range(a):
        for j in range(a):
            if M[i][j] > 0:
                par[find(i)] = find(a + j)
    r = find(0)
    return all(find(x) == r for x in range(2 * a))


def build_nb(MT, inv, a, N, d, lab, vol):
    """Regular neighbour array (V, d) of the lift.  A_i vertex g = i*N + g; B_j vertex h = (a+j)*N + h."""
    V = 2 * a * N
    NB = np.empty((V, d), dtype=np.int64)
    for i in range(a):
        for t in range(d):
            j = lab[i][t]
            NB[i * N:(i + 1) * N, t] = (a + j) * N + MT[:, vol[i][t]]
    for j in range(a):
        k = 0
        for i in range(a):
            for t in range(d):
                if lab[i][t] == j:
                    NB[(a + j) * N:(a + j + 1) * N, k] = i * N + MT[:, inv[vol[i][t]]]
                    k += 1
    return NB


def cost_of(NB, srcs, D, V):
    """Number of (source, vertex) pairs not reached within D steps, summed over the orbit representatives."""
    total = 0
    for s in srcs:
        vis = np.zeros(V, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = NB[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += V - int(np.count_nonzero(vis))
    return total


def anneal(MT, inv, a, N, d, D, lab, rng, deadline):
    """Simulated annealing over voltages within each (i, j) block (voltages in a block are distinct).
    Returns the voltage table with cost 0, or None at the deadline."""
    V = 2 * a * N
    srcs = [k * N for k in range(2 * a)]
    blocks = {}
    for i in range(a):
        for t in range(d):
            blocks.setdefault((i, lab[i][t]), []).append(t)

    def fresh():
        vol = [[0] * d for _ in range(a)]
        for (i, _j), ts in blocks.items():
            vals = rng.choice(N, size=len(ts), replace=False)
            for t, x in zip(ts, vals):
                vol[i][t] = int(x)
        return vol

    def score(vol):
        return cost_of(build_nb(MT, inv, a, N, d, lab, vol), srcs, D, V)

    temp, patience = 0.5, 1500
    vol = fresh()
    cur = score(vol)
    best, stale = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        i = int(rng.integers(a))
        t = int(rng.integers(d))
        j = lab[i][t]
        ts = blocks[(i, j)]
        used = {vol[i][u] for u in ts if u != t}
        bc, bx = None, None
        for _ in range(3):
            x = int(rng.integers(N))
            if x in used:
                continue
            old = vol[i][t]
            vol[i][t] = x
            c = score(vol)
            vol[i][t] = old
            if bc is None or c < bc:
                bc, bx = c, x
        if bx is None:
            continue
        delta = bc - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            vol[i][t] = bx
            cur = bc
            if cur < best:
                best, stale = cur, 0
        stale += 1
        if stale > patience:
            vol = fresh()
            cur = score(vol)
            best, stale = cur, 0
    return vol if cur == 0 else None


def lift_edges(NB):
    """Edge list of the lift; every edge is seen from its A endpoint, which has the smaller index."""
    V = NB.shape[0]
    edges = []
    for v in range(V):
        for u in NB[v].tolist():
            if v < u:
                edges.append((v, u))
    return V, edges


def search_lifts(d, D, seed, deadline):
    """Round-robin annealing over candidate lifts with orders above the baseline.  Returns the largest valid
    (n, edges) found, or None."""
    rng = np.random.default_rng(seed)
    cands = []
    for a, Ns in ((2, range(166, 181)), (3, range(111, 118)), (4, range(84, 89))):
        for N in Ns:
            V = 2 * a * N
            if V <= 660:
                continue
            Ms, seen = [], set()
            for _ in range(40):
                M = random_M(a, d, rng)
                key = tuple(map(tuple, M))
                if key in seen or not connected(M, a):
                    continue
                seen.add(key)
                Ms.append(M)
                if len(Ms) == 2:
                    break
            for g in meta_list(N)[:2]:
                for M in Ms:
                    cands.append((V, a, N, g, M))
    cands.sort(key=lambda c: (c[0], c[1]))

    groups = {}
    best, best_V = None, 0
    slice_s = 0.8
    while True:
        progressed = False
        for V, a, N, g, M in cands:
            if time.monotonic() >= deadline:
                return best
            if V <= best_V:
                continue
            progressed = True
            end = min(deadline, time.monotonic() + slice_s)
            if g not in groups:
                groups[g] = group_meta(*g)
            MT, inv = groups[g]
            lab = [[j for j in range(a) for _ in range(M[i][j])] for i in range(a)]
            vol = anneal(MT, inv, a, N, d, D, lab, rng, end)
            if vol is not None:
                NB = build_nb(MT, inv, a, N, d, lab, vol)
                n, edges = lift_edges(NB)
                if lib.is_valid(n, edges, d, D):
                    best, best_V = (n, edges), V
        if not progressed or time.monotonic() >= deadline:
            break
        slice_s *= 1.5
    return best


# ----------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph (A-vertex g ~ B-vertex s*g), checked; used if no lift is found."""
    try:
        MT, _inv = group_meta(33, 10, 26)
        S = sorted({0, 179, 116, 180, 47, 306})
        N = MT.shape[0]
        edges = sorted({(g, N + int(MT[s, g])) for s in S for g in range(N)})
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    try:
        res = search_lifts(d, D, seed, deadline)
        if res is not None:
            return res
    except Exception:
        pass
    return _fallback(d, D)
