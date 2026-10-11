import math
import random
import time

import lib

# Bold change: the parent's mixed pipeline is replaced for D >= 4 by a direct
# search over voltage lifts of bi-coset type. The base has k layers per side,
# and the group is a semidirect product Z_m x| Z_k2, sampled over many orders.
# Each layer has exactly d darts out and d darts in, so every degree is exactly d.
# Left multiplication by a group element is an automorphism of each layer, so
# eccentricity needs to be checked only from one representative per layer side.
# Validity is checked with lib.is_valid before any graph is returned.

_BIG = 10 ** 6
_SLICE_FRAC = 0.06   # time slice per annealing attempt, as a fraction of time_limit


def _perm(mul, G, s):
    """Right-multiplication permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _sample_group(G, rng):
    """Pick a random semidirect product Z_m x| Z_k2 of order G; return (order, mul) or None."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    if not opts:
        return None
    m, k2, r = rng.choice(opts)
    order, mul, _ = lib.semidirect_group(m, k2, r)
    return order, mul


def _cost(k, G, D, d, tgt, sv, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    keys = set()
    for L in range(d):
        for i in range(k):
            key = (i, tgt[L][i], sv[L][i])
            if key in keys:
                return _BIG          # parallel edges would lower degrees
            keys.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for L in range(d):
        for i in range(k):
            j = tgt[L][i]
            pm = perms[L][i]
            ba = i * G
            bb = (k + j) * G
            for g in range(G):
                a = ba + g
                b = bb + pm[g]
                adj[a].append(b)
                adj[b].append(a)
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in srcs:
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
    return total


def _to_graph(k, G, d, tgt, perms):
    """Expand the voltage structure into (n, edges)."""
    E = set()
    for L in range(d):
        for i in range(k):
            j = tgt[L][i]
            pm = perms[L][i]
            for g in range(G):
                a = i * G + g
                b = (k + j) * G + pm[g]
                E.add((min(a, b), max(a, b)))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, end):
    """Time-bounded simulated annealing; returns (n, edges) if a valid lift is found, else None."""
    tgt, sv, perms = [], [], []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        tgt.append(p)
        row = [rng.randrange(G) for _ in range(k)]
        sv.append(row)
        perms.append([_perm(mul, G, s) for s in row])

    cost = _cost(k, G, D, d, tgt, sv, perms)
    t_start = time.monotonic()
    span = max(1e-3, end - t_start)
    T0, T1 = 2.0, 0.15

    while cost > 0:
        now = time.monotonic()
        if now >= end:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)

        if k == 1 or rng.random() < 0.6:
            # Change one voltage.
            L = rng.randrange(d)
            i = rng.randrange(k)
            new_s = rng.randrange(G)
            old_s = sv[L][i]
            if new_s == old_s:
                continue
            old_p = perms[L][i]
            sv[L][i] = new_s
            perms[L][i] = _perm(mul, G, new_s)
            c2 = _cost(k, G, D, d, tgt, sv, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                sv[L][i] = old_s
                perms[L][i] = old_p
        else:
            # Swap two target layers within one level (keeps all degrees exact).
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            tgt[L][a], tgt[L][b] = tgt[L][b], tgt[L][a]
            c2 = _cost(k, G, D, d, tgt, sv, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                tgt[L][a], tgt[L][b] = tgt[L][b], tgt[L][a]

    if cost != 0:
        return None
    return _to_graph(k, G, d, tgt, perms)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback
    best = fallback

    # D = 3: incidence graph of PG(2, q), q the largest prime power <= d - 1.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if lib.is_valid(n, e, d, D):
                    best = (n, e)
                break
        return best

    # D >= 4: search over bi-coset voltage lifts with growing order.
    try:
        rng = random.Random(seed)
        ks = [1, 1, 2, 2, 3, 4, 6]
        slice_len = max(1.0, _SLICE_FRAC * time_limit)
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.2:
                break
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(d, 2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            end = now + min(remaining, slice_len)
            res = _anneal(d, D, k, order, mul, rng, end)
            if res is not None:
                n, e = res
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
