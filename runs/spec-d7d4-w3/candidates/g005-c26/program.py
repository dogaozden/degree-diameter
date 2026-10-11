import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar graphs H(m, S): a_i ~ b_{(i+s) mod m} for s in S, |S| = d.
# This is a bi-Cayley graph over Z_m. Translation by t maps a_i -> a_{i+t}
# and b_j -> b_{j+t}, and the map a_i <-> b_{-i} swaps the sides. So all
# distances are determined by BFS from a_0 and from b_0, and the graph has
# diameter <= D exactly when both BFS trees reach every vertex within D.
# Unlike the GQ/twin/lift pipeline, this family has no algebraic base graph.
# ----------------------------------------------------------------------------

def _haar_adj(m, S):
    adj = [None] * (2 * m)
    for i in range(m):
        adj[i] = [m + (i + s) % m for s in S]
    for j in range(m):
        adj[m + j] = [(j - s) % m for s in S]
    return adj


def _cost(m, S, D):
    """Number of vertices not reached within D steps from a_0 or from b_0 (0 means diameter <= D)."""
    adj = _haar_adj(m, S)
    N = 2 * m
    total = 0
    for src in (0, m):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _anneal(m, d, D, deadline, rng, iters):
    """Simulated annealing over connection sets S of size d in Z_m (0 is fixed in S by translation)."""
    if m < d or m < 2:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _cost(m, S, D)
    for it in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        T = 1.5 * (0.02 ** (it / iters))
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(m, S, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c = c2
        else:
            S[i] = old
    return list(S) if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Projective-plane incidence graph meets the Moore bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        if best[0] >= moore:
            return best

    # Main search: cyclic Haar graphs, ascending from a modest order.
    # Each success moves the target one step up; failures are retried with fresh restarts.
    target = max(d, int(0.6 * moore / 2))
    while time.monotonic() < deadline and target <= moore // 2:
        S = _anneal(target, d, D, deadline, rng, 2000)
        if S is not None:
            n, e = lib.haar_graph(target, S)
            if consider(n, e):
                target = max(target + 1, best[0] // 2 + 1)
                continue
            target += 1
        # Otherwise: fresh random restart at the same target.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
