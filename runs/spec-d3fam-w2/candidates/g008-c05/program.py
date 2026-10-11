import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _random_comp(d, p, rng):
    """Random composition of d into p positive parts (c_k = number of darts in each circulant class)."""
    if p == 1:
        return [d]
    cuts = sorted(rng.sample(range(1, d), p - 1))
    parts, prev = [], 0
    for c in cuts + [d]:
        parts.append(c - prev)
        prev = c
    return parts


def _nbrs(v, N, p, V):
    """Neighbours of vertex v in the lift.

    A-side vertex (i, x) is encoded as i*N + x; B-side vertex (j, y) as p*N + j*N + y.
    Block (i, j) holds the voltage set V[i][j]: A(i,x) ~ B(j, x+w) for each w in V[i][j].
    """
    if v < p * N:
        i, x = divmod(v, N)
        out = []
        for j in range(p):
            base = p * N + j * N
            for w in V[i][j]:
                out.append(base + (x + w) % N)
        return out
    j, y = divmod(v - p * N, N)
    out = []
    for i in range(p):
        for w in V[i][j]:
            out.append(i * N + (y - w) % N)
    return out


def _ball_size(s, N, p, V):
    """Number of vertices within distance 3 of s (BFS, depth 3)."""
    seen = {s}
    frontier = [s]
    for _ in range(3):
        nxt = []
        for v in frontier:
            for u in _nbrs(v, N, p, V):
                if u not in seen:
                    seen.add(u)
                    nxt.append(u)
        frontier = nxt
        if not frontier:
            break
    return len(seen)


def _anneal_lift(N, p, c, rng, end):
    """Search voltage sets on a p-by-p base (circulant dart counts c) over Z_N.

    The lift is vertex-transitive under translation of each side, so diameter <= 3 holds
    iff every base vertex (one per side per base index) has a ball of radius 3 covering
    the whole lift. The cost is the total number of uncovered vertices over those 2p balls.
    Returns the voltage sets V (V[i][j] = list of voltages) or None if time runs out.
    """
    M = [[c[(j - i) % p] for j in range(p)] for i in range(p)]
    V = [[rng.sample(range(N), M[i][j]) for j in range(p)] for i in range(p)]
    bases = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    n = 2 * p * N

    def cost():
        return sum(n - _ball_size(s, N, p, V) for s in bases)

    cur = cost()
    it = 0
    while cur > 0:
        if (it & 31) == 0 and time.monotonic() >= end:
            return None
        it += 1
        i = rng.randrange(p)
        j = rng.randrange(p)
        blk = V[i][j]
        if not blk:
            continue
        k = rng.randrange(len(blk))
        new = rng.randrange(N)
        if new in blk:
            continue
        old = blk[k]
        blk[k] = new
        nc = cost()
        delta = nc - cur
        T = 0.3 + 1.2 * (1.0 - (it % 4000) / 4000.0)  # sawtooth temperature
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = nc
        else:
            blk[k] = old
    return V


def _lift_edges(N, p, V):
    """Edge list and order of the lift defined by voltage sets V."""
    edges = []
    for i in range(p):
        for j in range(p):
            for w in V[i][j]:
                for x in range(N):
                    edges.append((i * N + x, p * N + j * N + (x + w) % N))
    return 2 * p * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Multi-base voltage lifts over Z_N: 2pN vertices, degree d, diameter 3.
    # p = 1 is the classical difference-cover (Haar-type) lift; p = 2, 3 use
    # several base vertices per side, which gives more room for large orders.
    ps = [2, 3, 1]
    hi = lib.moore_bound(d, D)
    N = max(d, min(best_n // (2 * p) + 1 for p in ps))
    while time.monotonic() < deadline:
        if 2 * N > hi:
            break
        active = [p for p in ps if best_n < 2 * p * N <= hi and N >= d]
        if not active:
            N += 1
            continue
        solved = False
        while not solved and time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            per_try = max(0.5, 0.15 * remaining)
            for p in active:
                now = time.monotonic()
                if now >= deadline:
                    break
                end = min(deadline, now + per_try)
                c = _random_comp(d, p, rng)
                V = _anneal_lift(N, p, c, rng, end)
                if V is not None:
                    try:
                        n, edges = _lift_edges(N, p, V)
                        consider(n, edges)
                    except Exception:
                        pass
                    solved = True
                    break
        if not solved:
            break
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
