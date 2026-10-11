import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k (annealed).
# ----------------------------------------------------------------------------

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


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
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
# NEW family: unstructured 2-switch annealing over d-regular bipartite graphs.
# Distance cost is computed with big-int bitsets for all vertices at once.
# ----------------------------------------------------------------------------

def _bad_pairs_bits(N, adj, D):
    """Number of unordered pairs at distance > D (unreachable counts as bad)."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nb = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(N - b.bit_count() for b in ball) // 2


def _rand_regular_bip(h, d, rng):
    """Edge set of a simple d-regular bipartite graph on h+h vertices (A index a, B index b), or None."""
    for _ in range(5000):
        E = set()
        ok = True
        for _ in range(d):
            p = list(range(h))
            rng.shuffle(p)
            for a in range(h):
                e = (a, p[a])
                if e in E:
                    ok = False
                    break
                E.add(e)
            if not ok:
                break
        if ok:
            return list(E)
    return None


def _anneal_bip(h, d, D, rng, deadline, T0=1.5, T1=0.05):
    """Try to find a simple d-regular bipartite graph with h+h vertices and diameter <= D."""
    E = _rand_regular_bip(h, d, rng)
    if E is None:
        return None
    N = 2 * h
    Ed = [list(e) for e in E]
    Eset = set(E)
    adj = [[] for _ in range(N)]
    for a, b in Ed:
        adj[a].append(h + b)
        adj[h + b].append(a)
    cost = _bad_pairs_bits(N, adj, D)
    start = time.monotonic()
    span = max(1e-6, deadline - start)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - start) / span)
        T = T0 * (T1 / T0) ** frac

        i = rng.randrange(len(Ed))
        j = rng.randrange(len(Ed))
        a1, b1 = Ed[i]
        a2, b2 = Ed[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue

        adj[a1].remove(h + b1)
        adj[h + b1].remove(a1)
        adj[a2].remove(h + b2)
        adj[h + b2].remove(a2)
        adj[a1].append(h + b2)
        adj[h + b2].append(a1)
        adj[a2].append(h + b1)
        adj[h + b1].append(a2)

        c2 = _bad_pairs_bits(N, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            Eset.discard((a1, b1))
            Eset.discard((a2, b2))
            Eset.add((a1, b2))
            Eset.add((a2, b1))
            Ed[i] = [a1, b2]
            Ed[j] = [a2, b1]
        else:
            adj[a1].remove(h + b2)
            adj[h + b2].remove(a1)
            adj[a2].remove(h + b1)
            adj[h + b1].remove(a2)
            adj[a1].append(h + b1)
            adj[h + b1].append(a1)
            adj[a2].append(h + b2)
            adj[h + b2].append(a2)

    if cost == 0:
        return N, [(a, h + b) for a, b in Ed]
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fast path: projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    lift_deadline = start + 0.35 * time_limit
    bip_deadline = start + 0.85 * time_limit

    # Phase 1: annealed group voltage lifts (the proven source of the current best).
    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < lift_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, lift_deadline, iters=1500)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2 (bold, new family): unstructured bipartite annealing, growing the order
    # one side at a time from just above the current best.
    if d <= 12:
        h = max(d, best_n // 2 + 1)
        attempt_len = max(3.0, 0.15 * time_limit)
        while time.monotonic() < bip_deadline:
            attempt_deadline = min(bip_deadline, time.monotonic() + attempt_len)
            res = _anneal_bip(h, d, D, rng, attempt_deadline)
            if res is not None:
                consider(res[0], res[1])
                h = res[0] // 2 + 1
            # On failure keep the same h and retry from a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
