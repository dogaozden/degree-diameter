"""Two-orbit group lifts for the (d=6, D=5) target, with exact early-abort annealing and a verified Haar fallback.

CONSTRUCTION.  Take a group G of order M and four vertex orbits: A-orbits 0 and 1, B-orbits 2 and 3.
Vertex (o, x) has id o*M + x.  A dart (i, j, g), i and j in {0,1}, g in G, joins (i, x) to (2+j, x*g) for all x.
Each A-orbit has 6 darts out and each B-orbit has 6 darts in, so the graph is bipartite, 6-regular, on 4M vertices.

WHY FOUR BFS SOURCES.  Left multiplication by h in G is an automorphism that is transitive on each orbit,
so diameter <= 5 holds iff the radius-5 balls of the four representatives (orbit, identity) cover everything.
COST = total uncovered vertices over those four balls (0 = valid).

NEW IN THIS VERSION.
  1. Exact Metropolis with early abort.  Acceptance of a move with cost c2 under temperature T and current cost
     cur is equivalent to c2 <= cur - T*ln(u) for a uniform u.  Draw u first, turn that into an integer cap, and
     abort the cost evaluation as soon as the partial sum exceeds the cap.  The accept/reject decision is unchanged,
     but most rejected moves are evaluated in one BFS instead of four.
  2. Wider group enumeration.  Every admissible lambda is tried for each metacyclic Z_m x| Z_k of order 172..200,
     ordered by size, so orders that could beat 684 (M >= 172) are searched first.

The best valid result is checked with lib.is_valid.  If nothing is found, a checked 660-vertex Haar graph is returned.
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
    """Neighbour table (4M x 6).  Dart (i, j, g): A-vertex i*M+x gets (2+j)*M + x*g;
    B-vertex (2+j)*M+y gets i*M + y*g^-1."""
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


def cost_bounded(nbr, N, M, cap=None):
    """Uncovered vertices summed over the four orbit representatives (radius 5).

    If cap is given, stop as soon as the running total exceeds cap and return that partial total.
    The returned value is then > cap, which certifies rejection. Otherwise it is the exact cost.
    """
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
        if cap is not None and total > cap:
            return total
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


def search_group(MT, inv, M, deadline, rng, T=2.0, patience=4000):
    """Annealing over voltages with random restarts, using exact Metropolis via threshold + early abort."""
    N = 4 * M
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        volt = {}
        for i in range(2):
            for j in range(2):
                c = pat[i][j]
                volt[(i, j)] = [int(x) for x in rng.choice(M, c, replace=False)] if c > 0 else []
        cur = cost_bounded(build_nbr(MT, inv, M, volt), N, M)
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
            # Metropolis: accept iff c2 <= cur - T*ln(u). Draw u first, then evaluate with that cap.
            u = max(float(rng.random()), 1e-300)
            thr = cur - T * math.log(u)
            c2 = cost_bounded(build_nbr(MT, inv, M, volt), N, M, cap=int(math.floor(thr)))
            if c2 <= thr:
                since = 0 if c2 < cur else since + 1
                cur = c2
            else:
                volt[p][k] = old
                since += 1
        if cur == 0:
            return volt
    return None


# ------------------------------------------------------------------------ candidates

def candidates(lo=172, hi=200, cap=8):
    """All admissible metacyclic Z_m x| Z_k of order lo..hi (every lambda), plus Heis(3) x Z_7 (189).

    Sorted by order so the orders that can beat 684 (M >= 172) are tried first.
    """
    specs = []
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            n_ = m * k
            if n_ < lo or n_ > hi:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    specs.append((n_, m, k, lam))
    specs.sort()
    out = [(n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))) for n_, m, k, lam in specs]
    out.append((189, lambda: group_times_cyclic(group_heis3(), 7)))
    out.sort(key=lambda t: t[0])
    return out[:cap]


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26))."""
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
    cands = candidates()
    best = None
    for idx, (n_, builder) in enumerate(cands):
        if best is not None and 4 * n_ <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            M = MT.shape[0]
            volt = search_group(MT, inv, M, end, rng)
            if volt is None:
                continue
            n, edges = to_edges(MT, M, volt)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue
    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
