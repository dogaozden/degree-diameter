import math
import random
import time

import lib

BIG = 10 ** 9


def _safe_fallback(d, D):
    """K_{d,d} (diameter 2, degree d) is valid for every D >= 2; K_2 for D = 1."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _alg_bases(d, D):
    """Algebraic diameter-3 graphs (valid for any D >= 3): PG(2,q) and Araujo-Pardo-Lopez."""
    out = []
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
        for q in range(min(d - 2, 23), 2, -1):
            if lib.is_prime_power(q):
                try:
                    out.append(lib.araujo_lopez_graph(q))
                except ValueError:
                    pass
                break
    return out


# ----------------------------------------------------------------------------
# Bold branch: bi-Cayley lifts over cyclic groups Z_m with a k+k base.
#
# Base: k A-vertices, k B-vertices, d "layers". Layer L is a permutation p_L of
# range(k) and gives darts (i, p_L[i], s). Every base vertex then has degree d.
# Lift: A_{i,g} ~ B_{j,g+s} for each dart (i, j, s). Z_m acts by translation,
# so distances from (i,g) equal distances from (i,0); only 2k BFS runs are needed.
# A dart list is a valid degree-d simple graph iff the triples (i, j, s) are distinct.
# ----------------------------------------------------------------------------

def _lift_cost(k, m, darts, D, reps, limit):
    """Count (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
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
        if total > limit:
            return total
    return total


def _anneal(d, D, k, m, rng, end, iters):
    """Simulated annealing over voltages and layer permutations; returns darts or None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    reps = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    cost = _lift_cost(k, m, darts, D, reps, float("inf"))
    t0 = time.monotonic()
    span = max(1e-6, end - t0)

    for it in range(iters):
        if cost == 0:
            break
        now = time.monotonic()
        if now >= end:
            break
        frac = max(it / iters, (now - t0) / span)
        T = 0.05 ** min(1.0, frac)
        limit = cost - T * math.log(1.0 - rng.random())

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(m)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _lift_cost(k, m, darts, D, reps, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, m, darts, D, reps, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    return darts if cost == 0 else None


def _lift_search(d, D, cur, rng, end, consider):
    """Repeatedly anneal lifts slightly larger than the current best; returns the best order."""
    fails = 0
    while time.monotonic() < end - 0.3:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        spread = 0.01 + 0.01 * min(fails, 15)
        target = cur * (1.0 + spread)
        m = max(2, math.ceil(target / (2 * k))) + rng.randrange(0, 2)
        run_end = min(end, time.monotonic() + 3.0)
        darts = _anneal(d, D, k, m, rng, run_end, 1500)
        if darts is None:
            fails += 1
            continue
        fails = 0
        N, edges = lib.voltage_lift(2 * k, [(i, k + j, s) for i, j, s in darts], m)
        cur = max(cur, consider(N, edges))
    return cur


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    best_n, best_e = _safe_fallback(d, D)
    if d < 1 or D <= 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
        return best_n

    for n, e in _alg_bases(d, D):
        consider(n, e)

    # Bold change for D >= 4: the cyclic bi-Cayley lift search is the main engine.
    if D >= 4 and time.monotonic() < deadline:
        _lift_search(d, D, best_n, rng, deadline, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return _safe_fallback(d, D)
    return best_n, best_e
