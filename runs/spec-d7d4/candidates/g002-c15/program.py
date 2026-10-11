import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley voltage search over Z_m (abelian), replacing the old group-lift
# annealing. Vertices: A_{i,g} = i*m + g and B_{j,h} = (k+j)*m + h.
# Each pair (i, j) carries C[i][j] distinct voltages s, joining A_{i,g} to
# B_{j,g+s} for all g. Row and column sums of C equal d, so the graph is
# d-regular and bipartite. Translation by Z_m is an automorphism, so the
# diameter check only needs BFS from one representative per layer.
# ----------------------------------------------------------------------------

def _best_pg3(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _random_matrix(k, d, rng):
    """Multiplicity matrix C (k x k) with all row and column sums equal to d, from d random permutations."""
    C = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            C[i][p[i]] += 1
    return C


def _adjacency(k, m, pairs, S):
    N = 2 * k * m
    adj = [[] for _ in range(N)]
    for i, j in pairs:
        ba = i * m
        bb = (k + j) * m
        for s in S[i][j]:
            for g in range(m):
                a = ba + g
                b = bb + (g + s) % m
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _cost(N, adj, reps, D):
    """Total number of vertices not within distance D of the representatives. Zero means valid."""
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _anneal(D, k, m, C, rng, iters, deadline):
    """Simulated annealing over the voltage sets. Returns (pairs, S) on success, else None."""
    pairs = [(i, j) for i in range(k) for j in range(k) if C[i][j] > 0]
    S = [[[] for _ in range(k)] for _ in range(k)]
    for i, j in pairs:
        S[i][j] = rng.sample(range(m), C[i][j])
    N = 2 * k * m
    reps = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    cost = _cost(N, _adjacency(k, m, pairs, S), reps, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i, j = pairs[rng.randrange(len(pairs))]
        lst = S[i][j]
        idx = rng.randrange(len(lst))
        new = rng.randrange(m)
        if new in lst:
            continue
        old = lst[idx]
        lst[idx] = new
        c2 = _cost(N, _adjacency(k, m, pairs, S), reps, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            lst[idx] = old
        T = max(0.05, T * 0.998)
    if cost == 0:
        return pairs, S
    return None


def _to_graph(k, m, pairs, S):
    E = []
    for i, j in pairs:
        for s in S[i][j]:
            for g in range(m):
                E.append((i * m + g, (k + j) * m + (g + s) % m))
    return 2 * k * m, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, which is optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    try:
        # D >= 3: projective plane incidence graph as a baseline.
        pg = _best_pg3(d)
        if pg is not None:
            consider(pg[0], pg[1])

        rng = random.Random(seed)
        ks = [1, 2, 3]
        cur = {k: d for k in ks}      # largest m found so far per k
        fails = {k: 0 for k in ks}

        # Climb: for each k, repeatedly try to grow m by one.
        while time.monotonic() < deadline:
            for k in ks:
                if time.monotonic() >= deadline:
                    break
                m = cur[k] + 1
                C = _random_matrix(k, d, rng)
                iters = 1500 * (1 + fails[k] // 4)
                res = _anneal(D, k, m, C, rng, iters, deadline)
                if res is not None:
                    pairs, S = res
                    n, e = _to_graph(k, m, pairs, S)
                    consider(n, e)
                    cur[k] = m
                    fails[k] = 0
                else:
                    fails[k] += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
