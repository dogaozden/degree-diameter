import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Haar graphs over semidirect products Z_m x| Z_k of order G.
#
# A_g ~ B_{g*s} for s in S (|S| = d). Left multiplication is an automorphism
# transitive on each side, so diameter <= D iff BFS from A_0 and B_0 reaches
# everything within D steps. The identity is kept in S (right-multiplying S by
# a fixed element gives an isomorphic graph), which shrinks the search space.
# ----------------------------------------------------------------------------

def _semidirect_candidates(G):
    """All (m, k, r) with m*k = G describing Z_m x| Z_k (k = 1 means cyclic)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _reach_bad(G, fwd, bwd, D):
    """Pairs (source, vertex) not reached within D steps from A_0 and from B_0. Zero iff valid.

    fwd[t][x] = x*s_t gives the B-neighbours of A_x; bwd[t][h] = h*s_t^{-1} gives the A-neighbours of B_h.
    """
    N = 2 * G
    bad = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for f in fwd:
                        v = G + f[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for b in bwd:
                        v = b[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        bad += N - cnt
    return bad


def _haar_anneal(G, d, D, mul, inv, rng, deadline):
    """Simulated annealing over connection sets S of size d (containing identity 0)."""
    cache = {}

    def pair(s):
        p = cache.get(s)
        if p is None:
            if len(cache) > 3000:
                cache.clear()
            p = ([mul(g, s) for g in range(G)], [mul(g, inv(s)) for g in range(G)])
            cache[s] = p
        return p

    def cost(S):
        ps = [pair(s) for s in S]
        return _reach_bad(G, [p[0] for p in ps], [p[1] for p in ps], D)

    S = [0] + rng.sample(range(1, G), d - 1)
    c = cost(S)
    T = 2.0
    stale = 0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        cand = S[:]
        cand[i] = x
        cc = cost(cand)
        if cc <= c or rng.random() < math.exp(-(cc - c) / T):
            stale = 0 if cc < c else stale + 1
            S, c = cand, cc
        else:
            stale += 1
        T = max(0.2, T * 0.999)
        if stale > 600:
            S = [0] + rng.sample(range(1, G), d - 1)
            c = cost(S)
            stale = 0
            T = 2.0
    return S if c == 0 else None


def _haar_search(d, D, seed, deadline):
    """Search Haar graphs over non-cyclic groups of growing order; return the largest valid (n, edges)."""
    rng = random.Random(seed * 1000003 + 17)
    moore = lib._moore_bound(d, D)
    lo = max(d + 1, (moore // 2) * 43 // 100)
    best = None
    best_G = None
    while time.monotonic() < deadline - 0.5:
        if best_G is None:
            G = rng.randint(lo, lo + 24)
        else:
            G = best_G + rng.randint(1, 3)
        cands = _semidirect_candidates(G)
        noncyc = [c for c in cands if c[1] > 1]
        cyc = [c for c in cands if c[1] == 1]
        rng.shuffle(noncyc)
        order_list = noncyc[:4] + cyc[:1]
        for m, k, r in order_list:
            now = time.monotonic()
            if now >= deadline - 0.5:
                break
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            if order != G:
                continue
            S = _haar_anneal(G, d, D, mul, inv, rng, min(deadline, now + 2.5))
            if S is None:
                continue
            edges = [(g, G + mul(g, s)) for g in range(G) for s in S]
            if lib.is_valid(2 * G, edges, d, D):
                best, best_G = (2 * G, edges), G
                break
    return best


# ----------------------------------------------------------------------------
# Annealed bi-Cayley voltage lifts over semidirect products (k base vertices per side).
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _vcost(k, G, D, darts, perms, limit=float("inf")):
    """Pairs (representative, vertex) not reached within D. Zero means valid."""
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
        if total > limit:
            return total
    return total


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _vanneal(d, D, k, G, mul, rng, deadline, iters):
    """Metropolis annealing over voltages and per-layer B-assignments. Returns (n, edges) or None."""
    darts = _random_darts(d, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _vcost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _vcost(k, G, D, darts, perms, limit)
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
            c2 = _vcost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, as (order, mul), or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
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


def _voltage_search(d, D, seed, deadline, best):
    """Repeatedly anneal voltage lifts above the current best order; keep any valid improvement."""
    rng = random.Random(seed * 7919 + d)
    ks = [1, 1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline - 0.2:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 4)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _vanneal(d, D, k, order, mul, rng, deadline, 1500 if k == 1 else 400)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.80 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    # Diameter-3 base: incidence graph of PG(2, q) with q the largest prime power <= d-1.
    if D >= 3:
        q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            try:
                n, e = lib.projective_plane_incidence(q)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except Exception:
                pass

    # New family: Haar graphs over non-cyclic semidirect products near order 342-350.
    if D >= 5 and d >= 4:
        try:
            hn = _haar_search(d, D, seed, t0 + 0.45 * total)
            if hn is not None and hn[0] > best[0] and lib.is_valid(hn[0], hn[1], d, D):
                best = hn
        except Exception:
            pass

    # Voltage-lift annealing gets the rest of the budget and can only improve.
    if D >= 5:
        try:
            best = _voltage_search(d, D, seed, t0 + total, best)
        except Exception:
            pass

    if best is None or not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
