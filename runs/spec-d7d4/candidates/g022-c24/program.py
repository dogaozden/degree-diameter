import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over finite groups.
# Vertices: A_{i,g} = i*G + g (side A) and B_{j,h} = (k+j)*G + h (side B).
# A dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g. Left translation by
# the group is an automorphism, so one representative per orbit suffices for
# the diameter check. Every A and B vertex has degree d (d layers, each a
# permutation i -> j), so the graph is bipartite, d-regular, and simple.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
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
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
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
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 0.8 * (0.02 ** (it / iters))
        limit = cost - T * math.log(1.0 - rng.random())

        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _group(G, rng):
    """Return (order, mul) for a group of order G: cyclic, or Z_m x| Z_k2."""
    opts = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(opts)
    for k2 in opts:
        m = G // k2
        if k2 == 1:
            order, mul, _ = lib.cyclic_group(m)
            return order, mul
        cands = [r for r in range(1, m)
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.8 * time_limit - 2.0)
    deadline = start + budget

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    mb = lib._moore_bound(d, D)
    if best[0] >= mb:
        return best

    try:
        # Exact record family for D = 3: projective plane when d-1 is a prime power.
        if D == 3 and lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e

        rng = random.Random(seed)
        target = max(best[0] + 2, int(0.70 * mb))
        fails = 0
        while time.monotonic() < deadline - 0.5:
            k = rng.choice([1, 1, 2, 2, 3, 4])
            G = -(-target // (2 * k)) + rng.randrange(0, 4)
            grp = _group(G, rng)
            if grp is None:
                fails += 1
                continue
            order, mul = grp
            slice_end = min(deadline, time.monotonic() + max(2.0, budget * 0.12))
            res = _anneal(d, D, k, order, mul, rng, slice_end, iters=2000)
            if res is not None:
                n, e = res
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                # Ratchet the target upward past the new best.
                target = max(target, best[0] + 2)
                fails = 0
            else:
                fails += 1
                if fails % 10 == 0:
                    target = max(best[0] + 1, int(target * 0.98))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
