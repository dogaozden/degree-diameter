import random
import time

import lib


# Idea: in a Z_m voltage lift, translation by Z_m is an automorphism of every
# fiber, so the eccentricity of (A_i, g) equals that of (A_i, 0). A diameter
# check therefore needs only 2k BFS runs (one per base vertex), not n. This
# makes voltage search over a multi-vertex balanced base fast enough for a
# hill climb that minimises the number of (source, vertex) pairs farther than D.

def _fallback(d, D):
    try:
        if d >= 1:
            n, e = lib.haar_graph(d, range(d))  # K_{d,d}
            if lib.is_valid(n, e, d, D):
                return n, e
    except Exception:
        pass
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


def _random_cell_counts(k, d, rng):
    """k x k nonnegative integer matrix with all row and column sums equal to d (sum of d permutations)."""
    c = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            c[i][p[i]] += 1
    return c


def _score(k, m, volt, D):
    """Count of (source, vertex) pairs not within distance D, for sources (A_i,0) and (B_j,0).

    Zero means the lift has diameter <= D. Vertex A(i,g) has id i*m+g;
    B(j,h) has id k*m + j*m + h.
    """
    N = 2 * k * m
    off = k * m
    aadj = [[] for _ in range(k)]
    badj = [[] for _ in range(k)]
    for i in range(k):
        for j in range(k):
            for a in volt[i][j]:
                aadj[i].append((j, a))
                badj[j].append((i, a))
    sources = [i * m for i in range(k)] + [off + j * m for j in range(k)]
    bad = 0
    for s in sources:
        dist = [-1] * N
        dist[s] = 0
        frontier = [s]
        seen = 1
        for depth in range(1, D + 1):
            nxt = []
            for x in frontier:
                if x < off:
                    i, g = divmod(x, m)
                    for j, a in aadj[i]:
                        y = off + j * m + (g + a) % m
                        if dist[y] < 0:
                            dist[y] = depth
                            nxt.append(y)
                else:
                    j, h = divmod(x - off, m)
                    for i, a in badj[j]:
                        y = i * m + (h - a) % m
                        if dist[y] < 0:
                            dist[y] = depth
                            nxt.append(y)
            seen += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += N - seen
    return bad


def _hill(k, m, d, D, rng, deadline, iters):
    """Random start, then hill climb on voltages; accepts moves that do not increase the score."""
    c = _random_cell_counts(k, d, rng)
    volt = [[rng.sample(range(m), c[i][j]) if c[i][j] else [] for j in range(k)]
            for i in range(k)]
    cells = [(i, j) for i in range(k) for j in range(k) if volt[i][j]]
    cur = _score(k, m, volt, D)
    it = 0
    while cur > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        i, j = rng.choice(cells)
        t = rng.randrange(len(volt[i][j]))
        new = rng.randrange(m)
        if new in volt[i][j]:
            continue
        old = volt[i][j][t]
        volt[i][j][t] = new
        s = _score(k, m, volt, D)
        if s <= cur:
            cur = s
        else:
            volt[i][j][t] = old
    return volt if cur == 0 else None


def _lift(k, m, volt, d):
    edges = []
    off = k * m
    for i in range(k):
        for j in range(k):
            for a in volt[i][j]:
                for g in range(m):
                    edges.append((i * m + g, off + j * m + (g + a) % m))
    return 2 * k * m, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 5.0)
    if budget < 1.0:
        budget = 0.5 * time_limit
    deadline = t0 + budget

    best = _fallback(d, D)

    # D = 3 with d-1 a prime power: projective plane incidence is optimal.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        try:
            n, e = lib.projective_plane_incidence(q)
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
        return best

    # Small or trivial cases: keep the fallback.
    if d < 2 or D <= 2:
        return best

    rng = random.Random(seed)
    ks = [1, 2, 3, 4]
    for idx, k in enumerate(ks):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(ks) - idx)
        k_deadline = now + share
        m = max(d + 1, best[0] // (2 * k) + 1)
        while time.monotonic() < k_deadline:
            volt = None
            for _ in range(2):
                volt = _hill(k, m, d, D, rng, k_deadline, 1200)
                if volt is not None or time.monotonic() >= k_deadline:
                    break
            if volt is None:
                break  # larger m for this k is harder; move to next k
            n, edges = _lift(k, m, volt, d)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            m += 1

    return best
