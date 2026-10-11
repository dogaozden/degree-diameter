import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite edge-switch annealing with vertex-insertion growth.
#
# State: a d-regular bipartite graph stored as Aadj[a] (list of B indices) and
# Badj[b] (list of A indices), with M vertices per side.
# Cost: number of unordered vertex pairs at distance > D.
# Moves: 2-switch (a1-b1, a2-b2) -> (a1-b2, a2-b1), which keeps all degrees.
# Growth: remove a matching of d edges, add one A vertex joined to the d
# former B endpoints and one B vertex joined to the d former A endpoints.
# This adds 2 vertices, keeps degrees, and creates a new valid-looking start
# state that annealing then repairs.
# ----------------------------------------------------------------------------


def _moore(d, D):
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _cost(M, Aadj, Badj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    N = 2 * M
    adj = [None] * N
    for a in range(M):
        adj[a] = [M + b for b in Aadj[a]]
    for b in range(M):
        adj[M + b] = Badj[b]
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _swap(Aadj, Badj, a1, i, a2, j):
    """Transpose the values Aadj[a1][i] and Aadj[a2][j]; self-inverse."""
    b1 = Aadj[a1][i]
    b2 = Aadj[a2][j]
    Aadj[a1][i] = b2
    Aadj[a2][j] = b1
    Badj[b1][Badj[b1].index(a1)] = a2
    Badj[b2][Badj[b2].index(a2)] = a1


def _grow(M, Aadj, Badj, d, rng):
    """Insert one new A vertex (index M) and one new B vertex (index M). Returns False on failure."""
    pairs = None
    for _ in range(40):
        order = list(range(M))
        rng.shuffle(order)
        used = set()
        cur = []
        for a in order:
            cands = [b for b in Aadj[a] if b not in used]
            if cands:
                b = rng.choice(cands)
                used.add(b)
                cur.append((a, b))
                if len(cur) == d:
                    break
        if len(cur) == d:
            pairs = cur
            break
    if pairs is None:
        return False
    for a, b in pairs:
        Aadj[a].remove(b)
        Badj[b].remove(a)
    Aadj.append([b for _, b in pairs])   # new A vertex M
    Badj.append([a for a, _ in pairs])   # new B vertex M
    for a, b in pairs:
        Badj[b].append(M)                # old B endpoint b -> new A vertex
        Aadj[a].append(M)                # old A endpoint a -> new B vertex
    return True


def _edges(M, Aadj):
    return [(a, M + b) for a in range(M) for b in Aadj[a]]


def _search(d, D, moore, M, Aadj, Badj, rng, end):
    """Anneal and grow. Returns (best_M, best_edges) for the largest zero-cost state seen, or None."""
    best = None
    cur = _cost(M, Aadj, Badj, D)
    chunk = 3000
    T0, T1 = 2.0, 0.2
    while time.monotonic() < end:
        if cur == 0:
            best = (M, _edges(M, Aadj))
            if 2 * M >= moore:
                break
            if _grow(M, Aadj, Badj, d, rng):
                M += 1
            else:
                # Could not grow: perturb with random switches and continue.
                for _ in range(20):
                    a1, a2 = rng.sample(range(M), 2)
                    i, j = rng.randrange(d), rng.randrange(d)
                    b1, b2 = Aadj[a1][i], Aadj[a2][j]
                    if b2 in Aadj[a1] or b1 in Aadj[a2]:
                        continue
                    _swap(Aadj, Badj, a1, i, a2, j)
            cur = _cost(M, Aadj, Badj, D)
            continue

        for step in range(chunk):
            if (step & 127) == 0 and time.monotonic() >= end:
                break
            a1, a2 = rng.sample(range(M), 2)
            i, j = rng.randrange(d), rng.randrange(d)
            b1, b2 = Aadj[a1][i], Aadj[a2][j]
            if b2 in Aadj[a1] or b1 in Aadj[a2]:
                continue
            _swap(Aadj, Badj, a1, i, a2, j)
            c2 = _cost(M, Aadj, Badj, D)
            delta = c2 - cur
            T = T0 * (T1 / T0) ** (step / chunk)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                if cur == 0:
                    break
            else:
                _swap(Aadj, Badj, a1, i, a2, j)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best_n, best_e

    moore = _moore(d, D)
    if best_n >= moore:
        return best_n, best_e

    # Seed: PG(2, d-1) incidence (d-regular, diameter 3) when available, else K_{d,d}.
    if d >= 3 and lib.is_prime_power(d - 1):
        n2, pe = lib.projective_plane_incidence(d - 1)
        M = n2 // 2
        Aadj = [[] for _ in range(M)]
        Badj = [[] for _ in range(M)]
        for u, v in pe:
            Aadj[u].append(v - M)
            Badj[v - M].append(u)
    else:
        M = d
        Aadj = [list(range(d)) for _ in range(d)]
        Badj = [list(range(d)) for _ in range(d)]

    budget = min(0.85 * time_limit, time_limit - 3.0)
    end = start + max(0.5, budget)
    rng = random.Random(seed * 131 + d * 7 + D)

    res = None
    try:
        res = _search(d, D, moore, M, Aadj, Badj, rng, end)
    except Exception:
        res = None

    if res is not None:
        n, e = 2 * res[0], res[1]
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
