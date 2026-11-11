"""Bi-Cayley (two-orbit) search for the bipartite degree-diameter problem at (d, D) = (6, 5).

CONSTRUCTION.  Take a metacyclic group G of order N and two copies of G as A-side orbits (A_0, A_1) and two
as B-side orbits (B_0, B_1).  A dart (i, j, s) joins A_i(g) to B_j(s*g) for all g.  Each (i, j) block holds a
set of group elements; with the block pattern [[a, 6-a], [6-a, a]] every vertex has degree 6.  The graph has
4N vertices, which beats the record 684 once N >= 172.

WHY THE CHECK IS CHEAP.  Right multiplication by h maps A_i(g) to A_i(gh) and preserves edges, so G acts
regularly on each orbit.  Diameter <= 5 therefore holds iff each of the four vertices A_0(e), A_1(e), B_0(e),
B_1(e) reaches every vertex within 5 steps.  The cost is the number of unreached vertices from those four
sources, computed with a numpy frontier BFS.  Cost 0 means valid.

SEARCH.  Simulated annealing over the block elements, with random restarts (and random block patterns) when
stuck.  Groups are visited in ascending order of order with adaptive time slices.  Every returned graph is
checked with lib.is_valid.  Fallbacks: a verified 660-vertex Haar graph over Z_33 x| Z_10, then K_{6,6}.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
PATTERNS = [
    [[3, 3], [3, 3]],
    [[4, 2], [2, 4]],
    [[2, 4], [4, 2]],
    [[5, 1], [1, 5]],
    [[1, 5], [5, 1]],
]
PATIENCE = 2500
TEMP = 1.2


# ------------------------------------------------------------------ groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with index a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Identity is index 0."""
    N = m * k
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    MT = MT.astype(np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def catalogue(lo, hi):
    """One non-abelian metacyclic group (N, m, k, lam) per order N in [lo, hi], in ascending order."""
    out = []
    for N in range(lo, hi + 1):
        found = None
        for k in range(2, 13):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    found = (N, m, k, lam)
                    break
            if found:
                break
        if found:
            out.append(found)
    return out


# ------------------------------------------------------------- the graph

def make_nbr(MT, inv, blocks, N):
    """Neighbour array (4N x 6). A_i(g) = i*N + g, B_j(h) = 2N + j*N + h."""
    nbr = np.empty((4 * N, 6), dtype=np.int64)
    ca = [0, 0]
    cb = [0, 0]
    for i in range(2):
        for j in range(2):
            for s in blocks[i][j]:
                nbr[i * N:(i + 1) * N, ca[i]] = 2 * N + j * N + MT[s]
                ca[i] += 1
    for j in range(2):
        for i in range(2):
            for s in blocks[i][j]:
                nbr[2 * N + j * N:2 * N + (j + 1) * N, cb[j]] = i * N + MT[inv[s]]
                cb[j] += 1
    return nbr


def ecc_unreached(nbr, src, levels=5):
    """Number of vertices not reached from src within `levels` steps."""
    n = nbr.shape[0]
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(levels):
        nxt = nbr[frontier].ravel()
        nxt = nxt[~seen[nxt]]
        if nxt.size == 0:
            break
        nxt = np.unique(nxt)
        seen[nxt] = True
        frontier = nxt
    return n - int(seen.sum())


def cost(nbr, N):
    """Total unreached count from the four orbit representatives. Zero means diameter <= 5."""
    return sum(ecc_unreached(nbr, s) for s in (0, N, 2 * N, 3 * N))


def anneal(MT, inv, N, deadline, rng):
    """Annealing with restarts. Returns (blocks, cost) for the best state seen."""
    best_blocks, best_c = None, 10 ** 9
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        blocks = [[rng.choice(N, size=pat[i][j], replace=False).tolist() for j in range(2)] for i in range(2)]
        cur = cost(make_nbr(MT, inv, blocks, N), N)
        since = 0
        while time.monotonic() < deadline and since < PATIENCE:
            i = int(rng.integers(2))
            j = int(rng.integers(2))
            blk = blocks[i][j]
            p = int(rng.integers(len(blk)))
            x = int(rng.integers(N))
            if x in blk:
                since += 1
                continue
            old = blk[p]
            blk[p] = x
            c = cost(make_nbr(MT, inv, blocks, N), N)
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                cur = c
                if cur < best_c:
                    best_c = cur
                    best_blocks = [[list(b) for b in row] for row in blocks]
                    since = 0
                    if cur == 0:
                        return best_blocks, 0
                else:
                    since += 1
            else:
                blk[p] = old
                since += 1
    return best_blocks, best_c


def sweep(seed, time_limit):
    """Visit groups in ascending order with adaptive slices; keep the largest checked valid graph."""
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.8 * time_limit - 4.0)
    rng = np.random.default_rng(seed)
    cats = catalogue(172, 232)
    best, best_n = None, 0
    for idx, (N, m, k, lam) in enumerate(cats):
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = len(cats) - idx
        slice_ = min(6.0, max(0.5, (deadline - now) / remaining))
        try:
            MT, inv = group_meta(m, k, lam)
            blocks, c = anneal(MT, inv, N, now + slice_, rng)
            if blocks is None or c != 0:
                continue
            nbr = make_nbr(MT, inv, blocks, N)
            n = 4 * N
            edges = [(r, int(v)) for r in range(2 * N) for v in nbr[r]]
            if n > best_n and lib.is_valid(n, edges, 6, 5):
                best, best_n = (n, edges), n
        except Exception:
            continue
    return best


# ------------------------------------------------------------ fallbacks

def haar_fallback():
    """Verified 660-vertex Haar graph over Z_33 x| Z_10 (checked at run time)."""
    MT, _ = group_meta(33, 10, 26)
    S = [0, 179, 116, 180, 47, 306]
    N = 330
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, 6, 5) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        g = sweep(seed, time_limit)
    except Exception:
        g = None
    if g is not None:
        return g
    try:
        g = haar_fallback()
        if g is not None:
            return g
    except Exception:
        pass
    return lib.haar_graph(6, range(6))
