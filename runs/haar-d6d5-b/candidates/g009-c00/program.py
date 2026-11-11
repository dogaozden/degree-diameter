"""Two-orbit group lifts for the (d=6, D=5) target, with a verified Haar fallback.

CONSTRUCTION.  Take a group G of order M.  Use four vertex orbits: A-orbits 0 and 1 and B-orbits 2 and 3.
Vertex (o, x) has id o*M + x.  A "dart" (i, j, g) with i in {0,1}, j in {0,1} and g in G joins
(i, x) to (2+j, x*g) for every x in G.  Each A-orbit needs 6 darts out and each B-orbit needs 6 darts in, so
the graph is bipartite and 6-regular with 4M vertices.  Distinct voltages within a pair (i, j) keep it simple.

WHY ONLY FOUR BFS SOURCES.  Left multiplication by h in G sends the edge (i, x)-(2+j, x*g) to
(i, h*x)-(2+j, h*x*g), so it is an automorphism that is transitive on each orbit.  Hence diameter <= 5 holds
iff the radius-5 ball of each of the four representatives (orbit, identity) covers all 4M vertices.
COST = total uncovered vertices over those four balls (0 = valid).

SEARCH.  Anytime round-robin over many candidate groups (all non-trivial lam choices, orders 166..200).
Each round gives every still-useful candidate a short annealing slice with random restarts, so no single
group consumes the whole budget.  Once a valid lift of order M is found, candidates that cannot beat it
(4*|G| <= best) are dropped.  Every result is checked with lib.is_valid; a checked smaller Haar graph
(660 vertices) is the fallback.
"""
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_heis3():
    """Heisenberg group mod 3 (order 27), element (a, b, c) -> a*9 + b*3 + c, identity 0."""
    p = 3
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // 9, (e // 3) % 3, e % 3
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * 9 + Bp * 3 + Cp)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    C = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    MT4 = MT0[:, None, :, None] * k + C[None, :, None, :]
    return _finish(MT4.reshape(n0 * k, n0 * k))


# ------------------------------------------------------------------------ two-orbit lift

PATTERNS = [
    [[3, 3], [3, 3]],
    [[2, 4], [4, 2]],
    [[4, 2], [2, 4]],
    [[1, 5], [5, 1]],
    [[5, 1], [1, 5]],
]


def build_nbr(MT, inv, M, volt):
    """Neighbour table (4M x 6).  Dart (i, j, g): A-vertex i*M+x gets neighbour (2+j)*M + x*g;
    B-vertex (2+j)*M+y gets neighbour i*M + y*g^-1."""
    N = 4 * M
    nbr = np.empty((N, 6), dtype=np.int64)
    ar = np.arange(M, dtype=np.int64)
    ca = [0, 0]
    cb = [0, 0]
    for (i, j), vs in volt.items():
        for g in vs:
            nbr[i * M + ar, ca[i]] = (2 + j) * M + MT[ar, g]
            ca[i] += 1
            nbr[(2 + j) * M + ar, cb[j]] = i * M + MT[ar, inv[g]]
            cb[j] += 1
    return nbr


def cost(nbr, N, M):
    """Uncovered vertices summed over the four orbit representatives, radius 5.  0 means diameter <= 5."""
    total = 0
    for s in (0, M, 2 * M, 3 * M):
        vis = np.zeros(N, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(5):
            nb = nbr[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += N - int(vis.sum())
    return total


def to_edges(MT, M, volt):
    ar = np.arange(M, dtype=np.int64)
    E = []
    for (i, j), vs in volt.items():
        for g in vs:
            u = i * M + ar
            v = (2 + j) * M + MT[ar, g]
            E.extend(zip(u.tolist(), v.tolist()))
    return 4 * M, [(int(a), int(b)) for a, b in E]


def search_group(MT, inv, M, deadline, rng, T=2.0, patience=3000):
    """Annealing over voltages with random restarts.  Returns a volt dict with cost 0, or None at deadline."""
    N = 4 * M
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        volt = {}
        for i in range(2):
            for j in range(2):
                c = pat[i][j]
                volt[(i, j)] = [int(x) for x in rng.choice(M, c, replace=False)] if c > 0 else []
        cur = cost(build_nbr(MT, inv, M, volt), N, M)
        pairs = [p for p in volt if volt[p]]
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur == 0:
                return volt
            p = pairs[int(rng.integers(len(pairs)))]
            k = int(rng.integers(len(volt[p])))
            x = int(rng.integers(M))
            if x in volt[p]:
                since += 1
                continue
            old = volt[p][k]
            volt[p][k] = x
            c2 = cost(build_nbr(MT, inv, M, volt), N, M)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                volt[p][k] = old
                since += 1
        if cur == 0:
            return volt
    return None


# ------------------------------------------------------------------------ candidates

def candidate_list(rng, cap=40):
    """Non-abelian groups of order 166..200 (every valid lam for each (m, k)), plus Heis(3) x Z_7 (189).

    Returns a list of (order, builder) pairs, randomly thinned to at most `cap` entries.
    """
    specs = []
    for m in range(3, 201):
        for k in range(2, 200 // m + 1):
            n_ = m * k
            if n_ < 166 or n_ > 200:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    specs.append((n_, m, k, lam))
    order = rng.permutation(len(specs)) if specs else []
    chosen = [specs[int(i)] for i in order[:cap - 1]]
    out = [(n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))) for n_, m, k, lam in chosen]
    out.append((189, lambda: group_times_cyclic(group_heis3(), 7)))
    return out


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26)), checked before return."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    edges = []
    for s in FALLBACK_S:
        for g in range(N):
            edges.append((g, N + int(MT[s, g])))
    return 2 * N, edges


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


# ------------------------------------------------------------------------ entry point

TARGET = (6, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    # Build all candidate tables once; each is small (order <= 200).
    states = []
    for n_, builder in candidate_list(rng):
        try:
            MT, inv = builder()
            states.append((int(MT.shape[0]), MT, inv))
        except Exception:
            continue

    best = None
    slice_len = 1.0
    while time.monotonic() < deadline:
        active = [s for s in states if best is None or 4 * s[0] > best[0]]
        if not active:
            break
        order = rng.permutation(len(active))
        for idx in order:
            M, MT, inv = active[int(idx)]
            if best is not None and 4 * M <= best[0]:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_len)
            try:
                volt = search_group(MT, inv, M, end, rng)
                if volt is None:
                    continue
                n, edges = to_edges(MT, M, volt)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
            except Exception:
                continue
        slice_len = min(4.0, slice_len * 1.25)

    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
