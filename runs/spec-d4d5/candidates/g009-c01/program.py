import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for degree d when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _is_regular(n, edges, d):
    """True if every vertex has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# NEW: regular bipartite switch-growth.
#
# A d-regular bipartite graph on N + N vertices is stored as a list E of pairs
# (a, b) with a in 0..N-1 (side A) and b in 0..N-1 (side B); the output vertex
# for b is N + b. Growth inserts one new A-vertex and one new B-vertex while
# keeping d-regularity exactly: choose a matching of d edges (a_i, b_i), replace
# each by (new_a, b_i) and add (a_i, new_b). Degrees are preserved everywhere.
# Double-edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) then anneal the number
# of vertex pairs at distance > D toward zero.
# ----------------------------------------------------------------------------

def _bad(N, E, D):
    """Number of unordered vertex pairs at distance > D in the graph encoded by E."""
    return lib.bad_pairs(2 * N, [(a, N + b) for a, b in E], D)


def _anneal_regular(N, E, D, rng, deadline, iters):
    """Anneal double-edge swaps on E (in place) until diameter <= D. Returns True on success."""
    S = set(E)
    M = len(E)
    cost = _bad(N, E, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = 1.0 * (1.0 - it / iters) + 0.05
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        E[i] = n1
        E[j] = n2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(n1)
        S.add(n2)
        c2 = _bad(N, E, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(n1)
            S.discard(n2)
            S.add((a1, b1))
            S.add((a2, b2))
    return cost == 0


def _insert_pair(N, E, d, rng):
    """Return a new (N+1, E') keeping d-regularity, or None if no matching is found."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedA, usedB, chosen = set(), set(), []
    for i in idx:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    E2 = list(E)
    new = N
    for i in chosen:
        a, b = E2[i]
        E2[i] = (new, b)
        E2.append((a, new))
    return N + 1, E2


def _switch_grow(d, D, n0, e0, moore, deadline, rng, consider):
    """Grow a d-regular diameter-D bipartite graph one vertex pair at a time, anneal each step."""
    N = n0 // 2
    E = [(u, v - N) for u, v in e0]
    good_N, good_E = N, E
    fails = 0
    while time.monotonic() < deadline:
        if 2 * (good_N + 1) > moore:
            break
        res = _insert_pair(good_N, good_E, d, rng)
        if res is None:
            break
        N2, E2 = res
        iters = 1500 * (1 + fails // 3)
        ok = _anneal_regular(N2, E2, D, rng, deadline, iters)
        if ok:
            good_N, good_E = N2, E2
            consider(2 * N2, [(a, N2 + b) for a, b in good_E])
            fails = 0
        else:
            fails += 1


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 (parent family).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _vcost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _vanneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _vcost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= moore:
        return best

    try:
        pg = _best_pg(d) if D >= 3 else None
        if D >= 3:
            ap = _araujo(d)
            if ap is not None:
                consider(ap[0], ap[1])
            if pg is not None:
                consider(pg[0], pg[1])

        # NEW family: regular switch-growth, started from a d-regular base.
        if D >= 3 and best_n < moore:
            if pg is not None and _is_regular(pg[0], pg[1], d):
                base_n, base_e = pg
            else:
                base_n, base_e = lib.haar_graph(d, range(d))
            if _is_regular(base_n, base_e, d):
                _switch_grow(d, D, base_n, base_e, moore,
                             start + 0.6 * time_limit, rng, consider)

        # Voltage lift search with the remaining time.
        if D >= 2:
            ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
            while time.monotonic() < deadline and best_n < moore:
                k = rng.choice(ks)
                base = best_n // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, 3))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _vanneal(d, D, k, order, mul, rng, deadline, 1500)
                if res is not None:
                    consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
