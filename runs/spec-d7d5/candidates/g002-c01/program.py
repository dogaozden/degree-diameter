import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x| Z_k2, searched by tabu search.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Layer L of darts is a permutation p_L of {0..k-1}; the dart (i, p_L(i), s)
# joins A_i,g to B_{p_L(i)}, g*s for every g. Each vertex then has degree d.
# Left translations are automorphisms, so checking distances from the 2k
# representatives suffices for diameter <= D.
#
# Search: tabu search over voltages and layer permutations, scoring a state
# by the number of (representative, vertex) pairs farther than D apart.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _perm(mul, G, s):
    """Right-translation permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
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


def _tabu(d, D, k, G, mul, rng, deadline, steps, sample):
    """Tabu search over voltages and layer permutations; returns (n, edges) or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_perm(mul, G, dt[2]) for dt in darts]
    cost = _cost(k, G, D, darts, perms)
    tabu_until = [0] * len(darts)
    tenure = 4

    for step in range(steps):
        if cost == 0 or time.monotonic() > deadline:
            break
        best_move = None
        best_c = None
        for _ in range(sample):
            if k == 1 or rng.random() < 0.75:
                idx = rng.randrange(len(darts))
                new = rng.randrange(G)
                old = darts[idx][2]
                if new == old:
                    continue
                oldp = perms[idx]
                darts[idx][2] = new
                perms[idx] = _perm(mul, G, new)
                c = _cost(k, G, D, darts, perms)
                darts[idx][2] = old
                perms[idx] = oldp
                move = ("v", idx, new)
                tabooed = tabu_until[idx] > step
            else:
                L = rng.randrange(d)
                a, b = rng.sample(range(k), 2)
                ia, ib = L * k + a, L * k + b
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                c = _cost(k, G, D, darts, perms)
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                move = ("s", ia, ib)
                tabooed = tabu_until[ia] > step or tabu_until[ib] > step
            # Aspiration: a tabu move is allowed only if it beats the current cost.
            if tabooed and c >= cost:
                continue
            if best_c is None or c < best_c:
                best_c = c
                best_move = move
        if best_move is None:
            continue
        if best_move[0] == "v":
            _, idx, new = best_move
            darts[idx][2] = new
            perms[idx] = _perm(mul, G, new)
            tabu_until[idx] = step + tenure
        else:
            _, ia, ib = best_move
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            tabu_until[ia] = step + tenure
            tabu_until[ib] = step + tenure
        cost = best_c

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(50):
        k2 = rng.choice([1, 1, 2, 3, 4, 6])
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


# ----------------------------------------------------------------------------
# Safe fallbacks.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: tabu-searched bi-Cayley lifts with growing group order.
    if D >= 3 and d >= 3:
        ks = [2, 3, 4, 5]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            attempt_end = min(deadline, time.monotonic() + 0.2 * time_limit)
            res = _tabu(d, D, k, order, mul, rng, attempt_end, steps=200, sample=10)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
