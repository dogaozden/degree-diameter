import math
import random
import time

import lib

BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Layer L of darts assigns A_i -> B_{p_L(i)} with voltage s, joining
# A_{i,g} to B_{p_L(i), mul(g, s)} for every group element g.
# Left multiplication is an automorphism, so BFS from one representative
# per layer on each side is enough to certify the diameter.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(60):
        k2 = rng.choice(choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
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


def _perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _build_adj(k, G, darts, perms):
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, G, D, adj, limit):
    """Unreached (representative, vertex) pairs within distance D. Zero means diameter <= D."""
    N = len(adj)
    for lst in adj:
        if len(set(lst)) != len(lst):
            return BIG  # parallel edge
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and layer targets. Returns (darts, perms) on success, else None."""
    darts = _random_darts(d, k, G, rng)
    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, _build_adj(k, G, darts, perms), float("inf"))
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm(mul, G, new_s)
            c2 = _cost(k, G, D, _build_adj(k, G, darts, perms), limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, _build_adj(k, G, darts, perms), limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return darts, perms
    return None


# ----------------------------------------------------------------------------
# Small-D helpers: projective plane / Araujo-Pardo-Lopez for D = 3,
# and a Haar-graph random search for D <= 4.
# ----------------------------------------------------------------------------

def _haar_search(d, D, rng, deadline, m0):
    """Random search over Haar graphs H(Z_m, S) with |S| = d; returns (n, edges) or None."""
    m = m0
    while time.monotonic() < deadline:
        if m - 1 >= d - 1 and m >= d:
            for _ in range(20):
                if time.monotonic() >= deadline:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, e = lib.haar_graph(m, S)
                if lib.bad_pairs(n, e, D) == 0:
                    return n, e
        m += 1
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D == 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                consider(*lib.araujo_lopez_graph(q))
            except Exception:
                pass

    if D <= 4:
        m0 = max(d, best_n // 2 + 1)
        res = _haar_search(d, D, rng, min(deadline, time.monotonic() + 0.3 * (deadline - start)), m0)
        if res is not None:
            consider(*res)
        if best_n < moore:
            # Keep a valid fallback; the remaining budget is not needed for D <= 4 targets here.
            pass
    else:
        ks = [1, 1, 1, 2, 2, 3]
        while time.monotonic() < deadline and best_n < moore:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            lo = max(2, base + 1)
            hi = lo + max(3, lo // 10)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            iters = 600 if k == 1 else 300
            res = _anneal(d, D, k, order, mul, rng, deadline, iters)
            if res is None:
                continue
            darts, perms = res
            N, E = _edges(k, order, darts, perms)
            consider(N, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
