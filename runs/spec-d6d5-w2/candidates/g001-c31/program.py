import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d}, projective plane incidence (D = 3), Araujo-Pardo-Lopez.
#
# Main new family (D >= 4): bi-Cayley voltage lifts over small groups
# Z_m x|_r Z_k2 with a bitset-based diameter cost, simulated annealing over
# voltages and layer permutations, and vertex-deletion repair for near misses.
# Every candidate passes lib.is_valid before it can replace the best graph.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _balls(N, adj, D):
    """Bitmask per vertex of all vertices within distance D (bit w set means w is reachable)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return reach


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [1] + [x for x in rng.sample(range(1, m), min(m - 1, 60))
                           if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _random_darts(d, k, G, rng):
    """d layers; each layer is a bijection i -> p(i) with a random voltage per dart."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _dup_pen(darts, G):
    """Penalty for repeated (i, j, s) darts, which would collapse into duplicate edges."""
    seen = set()
    pen = 0
    for t in darts:
        key = (t[0], t[1], t[2])
        if key in seen:
            pen += G
        seen.add(key)
    return pen


def _cost(k, G, D, darts, perms):
    """Unreached (representative, vertex) pairs at distance > D, plus duplicate penalty.

    Left multiplication by the group is an automorphism of the lift, so one representative
    per fibre suffices. Zero means the lift has diameter <= D.
    """
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reach = _balls(N, adj, D)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    return sum(N - reach[r].bit_count() for r in reps) + _dup_pen(darts, G)


def _edges(k, G, darts, perms):
    """Full lift as (n, sorted edge list). A-fibre vertices are 0..kG-1, B-fibre vertices follow."""
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and layer target permutations. Returns (darts, perms, cost)."""
    darts = _random_darts(d, k, G, rng)
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.5
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.15, T * 0.998)
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old_s, old_p = darts[idx][2], perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, perms, cost


def _repair(n, edges, D, min_n, deadline):
    """Delete the vertex with most unreached pairs, repeatedly, while staying >= min_n. None on failure."""
    cur_n, cur_e = n, list(edges)
    while cur_n > min_n and time.monotonic() < deadline:
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        reach = _balls(cur_n, adj, D)
        bad = [cur_n - r.bit_count() for r in reach]
        if not any(bad):
            return cur_n, cur_e
        drop = max(range(cur_n), key=lambda x: bad[x])
        remap = {}
        for v in range(cur_n):
            if v != drop:
                remap[v] = len(remap)
        cur_e = [(remap[u], remap[v]) for u, v in cur_e if u != drop and v != drop]
        cur_n -= 1
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    if D == 3:
        # Projective plane incidence graph, degree q + 1 <= d.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
        # Araujo-Pardo-Lopez graph for d = q + 2.
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                n, e = lib.araujo_lopez_graph(q)
                consider(n, e)
            except Exception:
                pass

    if D >= 4:
        # Voltage-lift search with ratcheting order target: every success raises best_n.
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            lo = best_n // (2 * k) + 1
            G = lo + rng.choice([0, 0, 0, 1, 2, 3])
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            darts, perms, c = _anneal(d, D, k, order, mul, rng, deadline, 1500)
            n, e = _edges(k, order, darts, perms)
            if c == 0:
                consider(n, e)
                continue
            if c <= 30 and time.monotonic() < deadline:
                rep_deadline = min(deadline, time.monotonic() + 3.0)
                out = _repair(n, e, D, best_n + 1, rep_deadline)
                if out is not None:
                    consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
