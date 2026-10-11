import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Distance counting on plain adjacency lists (bitset balls).
# ----------------------------------------------------------------------------

def _unreached(n, adj, D):
    """Number of ordered vertex pairs at distance greater than D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


# ----------------------------------------------------------------------------
# Phase B (new): edge-switch annealing on a d-regular bipartite graph.
# Sides A = 0..h-1 and B = h..2h-1. Each switch keeps the graph bipartite
# and regular. Cost = unreached ordered pairs.
# ----------------------------------------------------------------------------

def _switch_search(h, d, D, rng, deadline):
    n = 2 * h
    E = [[a, (a + s) % h] for a in range(h) for s in range(d)]
    S = {(a, b) for a, b in E}
    if len(S) != len(E):
        return None

    def make_adj():
        adj = [[] for _ in range(n)]
        for a, b in E:
            adj[a].append(h + b)
            adj[h + b].append(a)
        return adj

    cost = _unreached(n, make_adj(), D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t0) / span)
        T = 2.0 * (0.05 ** frac)
        p = rng.randrange(len(E))
        q = rng.randrange(len(E))
        if p == q:
            continue
        a1, b1 = E[p]
        a2, b2 = E[q]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        E[p] = [a1, b2]
        E[q] = [a2, b1]
        c2 = _unreached(n, make_adj(), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
            E[p] = [a1, b1]
            E[q] = [a2, b2]
    if cost == 0:
        return [(a, b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# Phase A (kept from parent): bi-Cayley voltage lifts over semidirect products.
# Distances are measured only from one representative per (side, layer),
# because left multiplication by a group element is an automorphism.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(60):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 50))
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


def _cost_bc(k, G, darts, R, D):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        Rs = R[s]
        ai = i * G
        bj = (k + j) * G
        for g in range(G):
            a = ai + g
            b = bj + Rs[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _anneal_bc(k, G, d, R, D, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost_bc(k, G, darts, R, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost_bc(k, G, darts, R, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_bc(k, G, darts, R, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts if cost == 0 else None


def _bc_edges(k, G, darts, R):
    E = set()
    for i, j, s in darts:
        Rs = R[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + Rs[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    phase_a_end = start + 0.30 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, which has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)

    def consider(n, e):
        nonlocal best, best_n
        if best_n < n <= moore and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        # Plain projective plane of order q with q + 1 <= d.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

        # Araujo-Pardo & Lopez record graph when d-2 is a prime power >= 3.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass

        # Phase A: bi-Cayley voltage lifts, as in the parent.
        while time.monotonic() < phase_a_end:
            k = rng.choice([1, 1, 2, 3])
            G = max(2, best_n // (2 * k) + 1 + rng.randrange(0, 2))
            if 2 * k * G > moore:
                k = 1
                G = best_n // 2 + 1
                if 2 * G > moore:
                    break
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            R = [[mul(x, s) for x in range(order)] for s in range(order)]
            darts = _anneal_bc(k, order, d, R, D, rng, phase_a_end, 1200)
            if darts is not None:
                n, e = _bc_edges(k, order, darts, R)
                consider(n, e)

        # Phase B (new): annealed edge switches on a d-regular bipartite graph
        # one size above the current best.
        while time.monotonic() < deadline:
            h = best_n // 2 + 1
            if 2 * h > moore or d > h:
                break
            now = time.monotonic()
            slice_end = min(deadline, now + max(4.0, (deadline - now) / 3))
            E = _switch_search(h, d, D, rng, slice_end)
            if E is not None:
                consider(2 * h, [(a, h + b) for a, b in E])
    except Exception:
        pass

    try:
        valid = lib.is_valid(best[0], best[1], d, D)
    except Exception:
        valid = False
    if not valid:
        best = lib.haar_graph(d, range(d))
    return best
