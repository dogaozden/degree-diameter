import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective-plane and Araujo-Pardo--Lopez bases (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez record graph when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every group element g.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8])
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


def _cost(k, G, D, darts, perms):
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


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

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
            c2 = _cost(k, G, D, darts, perms)
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
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Switch search on balanced d-regular bipartite graphs (new family).
# Start from a random Haar graph on m + m vertices and apply double-edge
# swaps, which preserve regularity and simplicity, minimizing the number of
# vertex pairs at distance more than D.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of unordered pairs at distance > D (bitset balls)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(n - b.bit_count() for b in ball) // 2


def _switch_anneal(n, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on n = 2m vertices; return edges or None."""
    m = n // 2
    S = rng.sample(range(m), d)
    E = [[a, (a + s) % m] for a in range(m) for s in S]
    have = {(a, b) for a, b in E}
    L = len(E)

    def cost():
        adj = [[] for _ in range(n)]
        for a, b in E:
            adj[a].append(m + b)
            adj[m + b].append(a)
        return _bad_count(n, adj, D)

    cur = cost()
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        i = rng.randrange(L)
        j = rng.randrange(L)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in have or (a2, b1) in have:
            continue
        have.discard((a1, b1))
        have.discard((a2, b2))
        have.add((a1, b2))
        have.add((a2, b1))
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        new = cost()
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            have.discard((a1, b2))
            have.discard((a2, b1))
            have.add((a1, b1))
            have.add((a2, b2))
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    if cur == 0:
        return [(a, m + b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    try:
        if d == 2:
            # Even cycle C_{2D} has max degree 2 and diameter D.
            consider(*lib.haar_graph(D, [0, 1]))
            return best

        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(*pg)
            ap = _araujo(d)
            if ap is not None:
                consider(*ap)

            # Phase 1: annealed group voltage lifts (about 30% of the budget).
            volt_end = start + 0.3 * (deadline - start)
            ks = [1, 1, 2, 2, 3, 4]
            while time.monotonic() < volt_end:
                k = rng.choice(ks)
                base = best[0] // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, 3))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, volt_end, 1500)
                if res is not None:
                    consider(*res)

            # Phase 2: switch search, aiming one step above the current best.
            while time.monotonic() < deadline - 0.5:
                now = time.monotonic()
                m = best[0] // 2 + 1
                dl = min(deadline, now + max(2.0, 0.5 * (deadline - now)))
                E = _switch_anneal(2 * m, d, D, rng, dl)
                if E is not None:
                    consider(2 * m, E)
    except Exception:
        pass

    n, e = best
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
