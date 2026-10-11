import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Different family: cyclic bi-lifts of a RANDOM base multigraph.
#
# Base: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. The base is a
# d-regular bipartite multigraph given by d "layers"; layer L is a permutation
# pi_L of range(k) (so the darts are (i, pi_L(i), s)). Each dart (i, j, s) lifts
# to edges A_{i,g} -- B_{j,(g+s) mod m} for all g in Z_m.
#
# Z_m translations are automorphisms, so distances from A_{i,0} and B_{j,0}
# represent every vertex of that fibre. The search anneals over voltages and
# over layer permutations (which keep the base d-regular) to drive the number
# of pairs at distance > D to zero, with N = 2*k*m just above the current best.
# ----------------------------------------------------------------------------

def _bi_cost(k, m, D, darts):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * k * m
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ba = i * m
        bb = (k + j) * m
        for g in range(m):
            a = ba + g
            b = bb + (g + s) % m
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    total = 0
    for src in reps:
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


def _bi_edges(k, m, darts):
    E = set()
    for i, j, s in darts:
        for g in range(m):
            a = i * m + g
            b = (k + j) * m + (g + s) % m
            E.add((min(a, b), max(a, b)))
    return 2 * k * m, sorted(E)


def _bi_anneal(d, D, k, m, rng, deadline, iters):
    """Anneal over voltages and layer permutations; return darts with zero cost, or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    cost = _bi_cost(k, m, D, darts)
    if cost == 0:
        return darts

    T0 = max(1.0, 0.03 * cost)
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters))
    T = T0

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(m)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            c2 = _bi_cost(k, m, D, darts)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                if cost == 0:
                    return darts
            else:
                darts[idx][2] = old_s
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _bi_cost(k, m, D, darts)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                if cost == 0:
                    return darts
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            ap = _araujo(d)
            if ap is not None:
                consider(ap[0], ap[1])
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])

        # Main search: annealed cyclic bi-lifts of random d-regular base multigraphs.
        # Each attempt targets an order strictly above the current best.
        ks = [2, 3, 4, 5, 6] if D >= 4 else [2, 3, 4]
        iters = 3000
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            target = best_n + 1 + rng.randrange(0, 4)
            m = max(2, -(-target // (2 * k)))  # ceil so that 2*k*m >= target
            darts = _bi_anneal(d, D, k, m, rng, deadline, iters)
            if darts is not None:
                n, e = _bi_edges(k, m, darts)
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
