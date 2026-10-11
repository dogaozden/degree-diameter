import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _pg_base(d, D, consider):
    if D < 3:
        return
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
            return


# ----------------------------------------------------------------------------
# Fast diameter measurement on an adjacency-list graph (bitmask balls).
# ----------------------------------------------------------------------------

def _fast_bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# NEW FAMILY: direct double-edge-swap annealing on d-regular bipartite graphs.
#
# Sides A = {0..s-1} and B = {s..2s-1}; every vertex has degree exactly d.
# A double-edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keeps all degrees and
# bipartiteness. We anneal the number of vertex pairs at distance > D to zero.
# ----------------------------------------------------------------------------

def _anneal_regular(s, d, D, rng, deadline, max_iters):
    """Return (n, edges) of a d-regular bipartite graph on 2s vertices with diameter <= D, or None."""
    n = 2 * s
    E = [(a, (a + t) % s) for t in range(d) for a in range(s)]  # simple: offsets distinct
    S = set(E)
    if len(S) != len(E):
        return None
    m = len(E)

    def build_adj():
        adj = [[] for _ in range(n)]
        for a, b in E:
            adj[a].append(s + b)
            adj[s + b].append(a)
        return adj

    cost = _fast_bad(n, build_adj(), D)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    T0 = 2.0
    T = T0
    it = 0
    while cost > 0 and it < max_iters:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t_start) / span
            T = max(0.05, T0 * (1.0 - frac))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = _fast_bad(n, build_adj(), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cost = c2
        else:
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)

    if cost == 0:
        return n, [(a, s + b) for a, b in E]
    return None


def _swap_phase(d, D, s, rng, deadline, consider):
    """Grow the side size s while annealing succeeds; stop at the Moore bound or the deadline."""
    bound = lib.moore_bound(d, D)
    while time.monotonic() < deadline and 2 * s <= bound and s >= d:
        now = time.monotonic()
        attempt_deadline = min(deadline, now + max(3.0, 0.6 * (deadline - now)))
        res = _anneal_regular(s, d, D, rng, attempt_deadline, 10 ** 9)
        if res is None:
            break
        consider(res[0], res[1])
        s += 1


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k (kept from parent).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


def _voltage_phase(d, D, rng, deadline, consider, get_best_n):
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    iters = 1500 if D >= 5 else 400
    while time.monotonic() < deadline:
        best_n = get_best_n()
        k = rng.choice(ks)
        base = best_n // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _vanneal(d, D, k, order, mul, rng, deadline, iters)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    state = {'best': fallback}

    def consider(n, e):
        if n > state['best'][0] and lib.is_valid(n, e, d, D):
            state['best'] = (n, e)

    def best_n():
        return state['best'][0]

    total = 0.85 * time_limit
    rng = random.Random(seed)
    try:
        _pg_base(d, D, consider)

        if d >= 3 and D >= 3:
            # Bold new family: swap-annealed regular bipartite graphs.
            s0 = max(d, best_n() // 2 + 1)
            _swap_phase(d, D, s0, rng, start + 0.50 * total, consider)

        # Voltage-lift family for the remaining budget.
        _voltage_phase(d, D, rng, start + total, consider, best_n)
    except Exception:
        pass  # keep the best valid graph found so far

    best = state['best']
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
