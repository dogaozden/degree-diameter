import math
import random
import time

import numpy as np

import lib


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G as (m, k2, r), or None."""
    opts = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(opts)
    for k2 in opts[:8]:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def _nbr_edges(k, G, d, volt, perm, R):
    """Dart lift: A_{i,g} = i*G+g, B_{j,h} = (k+j)*G+h; layer L joins A_i to B_{perm[L][i]} via g -> g*volt."""
    N = 2 * k * G
    g = np.arange(G, dtype=np.int64)
    srcs, dsts = [], []
    for L in range(d):
        for i in range(k):
            j = int(perm[L][i])
            s = int(volt[L][i])
            srcs.append(i * G + g)
            dsts.append((k + j) * G + R[s])
    return N, np.concatenate(srcs), np.concatenate(dsts)


def _nbr(N, src, dst, d):
    """Adjacency as an (N, d) array; the lift is d-regular so every vertex appears exactly d times."""
    allv = np.concatenate([src, dst])
    other = np.concatenate([dst, src])
    order = np.argsort(allv, kind="stable")
    return other[order].reshape(N, d)


def _cost(nbr, N, reps, D, limit):
    """Total number of vertices not reached within D steps from the class representatives."""
    total = 0
    for s0 in reps:
        seen = np.zeros(N, dtype=bool)
        seen[s0] = True
        frontier = np.array([s0], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[frontier].ravel()
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            seen[nxt] = True
            frontier = nxt
        total += N - int(seen.sum())
        if total > limit:
            return total
    return total


def _search(d, D, k, G, R, rng, deadline, iters):
    """Anneal voltages and layer permutations until the lift has diameter <= D. Returns (volt, perm) or None."""
    volt = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    perm = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]

    def evaluate(limit):
        N, src, dst = _nbr_edges(k, G, d, volt, perm, R)
        nb = _nbr(N, src, dst, d)
        return _cost(nb, N, reps, D, limit)

    cost = evaluate(math.inf)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.996)
        limit = cost - T * math.log(1.0 - rng.random())
        if k > 1 and rng.random() < 0.3:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            perm[L, a], perm[L, b] = perm[L, b], perm[L, a]
            c2 = evaluate(limit)
            if c2 <= limit:
                cost = c2
            else:
                perm[L, a], perm[L, b] = perm[L, b], perm[L, a]
        else:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = int(volt[L, i])
            volt[L, i] = rng.randrange(G)
            c2 = evaluate(limit)
            if c2 <= limit:
                cost = c2
            else:
                volt[L, i] = old
    if cost == 0:
        return volt.copy(), perm.copy()
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    moore = _moore(d, D)
    if best_n >= moore or d < 2 or D < 2:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Main search: bi-Cayley dart lifts over semidirect products, annealed for diameter D.
    # Each attempt targets a slightly larger order than the current best.
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        lo = best_n // (2 * k) + 1
        if lo < 2:
            lo = 2
        G = rng.randint(lo, lo + max(3, lo // 12))
        g = _sample_group(G, rng)
        if g is None:
            continue
        m, k2, r = g
        _, mul, _ = lib.semidirect_group(m, k2, r)
        R = np.array([[mul(x, s) for x in range(G)] for s in range(G)], dtype=np.int64)

        attempt_deadline = min(deadline, time.monotonic() + 8.0)
        iters = 1500 if k == 1 else 600
        res = _search(d, D, k, G, R, rng, attempt_deadline, iters)
        if res is None:
            continue
        volt, perm = res
        N, src, dst = _nbr_edges(k, G, d, volt, perm, R)
        E = set()
        for u, v in zip(src.tolist(), dst.tolist()):
            E.add((u, v) if u < v else (v, u))
        consider(N, sorted(E))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
