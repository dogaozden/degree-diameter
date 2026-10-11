import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 4000        # initial annealing steps per growth attempt
MAX_ANNEAL_ITERS = 60000   # cap after repeated failures
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Structured baselines (kept as safe fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New engine: d-regular bipartite graphs grown one vertex per side at a time.
#
# Representation: F has shape (2N, d). Vertices 0..N-1 are side A, N..2N-1 are
# side B. F[a] lists the B-neighbours of a (global ids), F[N+b] lists the
# A-neighbours of B-vertex b.
#
# Each size N is reached by:
#   1. Growth: add one A and one B vertex. Pick d disjoint edges (a_i, b_i),
#      delete them, and join the new A vertex to every b_i and the new B vertex
#      to every a_i. Degrees are preserved and the graph stays simple.
#   2. Annealing: random double-edge switches, scored by the number of
#      unordered vertex pairs farther than D apart. Cost 0 means a valid graph.
# Distances are computed with bitsets over all vertices in numpy.
# ----------------------------------------------------------------------------

def _from_pairs(N, pairs, d):
    """Build F from local (a, b) pairs; return None unless the graph is d-regular."""
    A = [[] for _ in range(N)]
    B = [[] for _ in range(N)]
    for a, b in pairs:
        A[a].append(N + b)
        B[b].append(a)
    F = np.empty((2 * N, d), dtype=np.int64)
    for v in range(N):
        if len(A[v]) != d:
            return None
        F[v] = A[v]
    for b in range(N):
        if len(B[b]) != d:
            return None
        F[N + b] = B[b]
    return F


def _edges_of(F, N, d):
    return [(a, int(F[a, s])) for a in range(N) for s in range(d)]


def _R0(N):
    """Initial reachability bitsets: each vertex reaches itself."""
    M = 2 * N
    idx = np.arange(M, dtype=np.int64)
    R0 = np.zeros((M, (M + 63) // 64), dtype=np.uint64)
    R0[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    return R0


def _unreached(F, R0, D):
    """Number of unordered vertex pairs at distance > D (0 means valid)."""
    M = R0.shape[0]
    R = R0.copy()
    for _ in range(D):
        Rn = R | np.bitwise_or.reduce(R[F], axis=1)
        if np.array_equal(Rn, R):
            break
        R = Rn
    pop = int(_POP8[R.view(np.uint8)].sum())
    return (M * M - pop) // 2


def _anneal(F, N, d, D, R0, rng, deadline, iters):
    """Edge-switch annealing on F in place. Returns (success, final_cost)."""
    E = _unreached(F, R0, D)
    if E == 0:
        return True, 0
    T0 = max(0.5, 0.05 * E)
    T_end = 0.2
    decay = (T_end / T0) ** (1.0 / max(1, iters))
    T = T0
    for it in range(iters):
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T *= decay
        a1 = rng.randrange(N)
        a2 = rng.randrange(N)
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        b1 = int(F[a1, i])
        b2 = int(F[a2, j])
        if b1 == b2:
            continue
        if (F[a1] == b2).any() or (F[a2] == b1).any():
            continue
        k1 = int(np.argmax(F[b1] == a1))
        k2 = int(np.argmax(F[b2] == a2))
        F[a1, i] = b2
        F[a2, j] = b1
        F[b1, k1] = a2
        F[b2, k2] = a1
        E2 = _unreached(F, R0, D)
        delta = E2 - E
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E = E2
            if E == 0:
                return True, 0
        else:
            F[a1, i] = b1
            F[a2, j] = b2
            F[b1, k1] = a1
            F[b2, k2] = a2
    return E == 0, E


def _grow(F, N, d, rng):
    """Return a d-regular graph on N+1 per side obtained by vertex insertion, or None."""
    pairs = [(a, int(F[a, s]) - N) for a in range(N) for s in range(d)]
    As = Bs = None
    for _ in range(50):
        cand_a = rng.sample(range(N), d)
        cand_b = [int(F[a, rng.randrange(d)]) - N for a in cand_a]
        if len(set(cand_b)) == d:
            As, Bs = cand_a, cand_b
            break
    if As is None:
        return None
    removed = set(zip(As, Bs))
    newpairs = [p for p in pairs if p not in removed]
    newpairs += [(N, b) for b in Bs]
    newpairs += [(a, N) for a in As]
    return _from_pairs(N + 1, newpairs, d)


def _engine(d, D, moore, rng, deadline, offer):
    """Grow a valid d-regular bipartite graph as far as time and the Moore bound allow."""
    N = d
    F = _from_pairs(N, [(a, b) for a in range(N) for b in range(N)], d)  # K_{d,d}
    iters = ANNEAL_ITERS
    while time.monotonic() < deadline and 2 * (N + 1) <= moore:
        Fg = _grow(F, N, d, rng)
        if Fg is None:
            continue
        R0 = _R0(N + 1)
        ok, _ = _anneal(Fg, N + 1, d, D, R0, rng, deadline, iters)
        if ok:
            if not offer(2 * (N + 1), _edges_of(Fg, N + 1, d)):
                return
            F = Fg
            N += 1
        else:
            iters = min(int(iters * 1.5), MAX_ANNEAL_ITERS)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is d-regular bipartite: the safe fallback.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def offer(n, e):
        """Accept (n, e) if valid; keep it as best if it is larger. Returns validity."""
        nonlocal best, best_n
        if not lib.is_valid(n, e, d, D):
            return False
        if n > best_n:
            best = (n, e)
            best_n = n
        return True

    # Structured baselines.
    if D == 3 and lib.is_prime_power(d - 1):
        pg = lib.projective_plane_incidence(d - 1)
        offer(pg[0], pg[1])
        return best
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            offer(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            offer(gq[0], gq[1])

    # Main search: grow d-regular bipartite graphs by annealing.
    if best_n < moore:
        try:
            _engine(d, D, moore, rng, deadline, offer)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
