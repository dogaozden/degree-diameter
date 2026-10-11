import math
import random
import time

import lib


def _groups_of_order(G):
    """All semidirect products Z_m x| Z_k (m*k = G, m >= 2) as (m, k, r) triples. Cyclic groups have k = 1."""
    cands = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    return cands


def _unreached(G, D, fwd, bwd, side, src):
    """Count vertices NOT within distance D of the source vertex (side 0 = A, side 1 = B, index src)."""
    seen_a = bytearray(G)
    seen_b = bytearray(G)
    if side == 0:
        seen_a[src] = 1
        fa, fb = [src], []
    else:
        seen_b[src] = 1
        fa, fb = [], [src]
    count = 1
    for _ in range(D):
        if not fa and not fb:
            break
        na, nb = [], []
        for x in fa:
            for P in fwd:
                y = P[x]
                if not seen_b[y]:
                    seen_b[y] = 1
                    nb.append(y)
        for y in fb:
            for Q in bwd:
                x = Q[y]
                if not seen_a[x]:
                    seen_a[x] = 1
                    na.append(x)
        count += len(na) + len(nb)
        fa, fb = na, nb
    return 2 * G - count


def _search_group(m, k, r, d, D, rng, end):
    """Hill-climb a d-element connection set S in G = Z_m x| Z_k so the bipartite Cayley graph
    (a_x ~ b_{x*g}, g in S) has diameter <= D. Returns (n, edges) or None if time runs out.

    Left translations act transitively on each side, so BFS from a_0 and b_0 decides diameter <= D.
    """
    G, mul, inv = lib.semidirect_group(m, k, r)
    if d > G:
        return None
    cache = {}

    def perms(g):
        p = cache.get(g)
        if p is None:
            ig = inv(g)
            p = ([mul(x, g) for x in range(G)], [mul(y, ig) for y in range(G)])
            cache[g] = p
        return p

    def score(S):
        ps = [perms(g) for g in S]
        fwd = [p[0] for p in ps]
        bwd = [p[1] for p in ps]
        return _unreached(G, D, fwd, bwd, 0, 0) + _unreached(G, D, fwd, bwd, 1, 0)

    S = rng.sample(range(G), d)
    cur = score(S)
    stall = 0
    while cur > 0:
        if time.monotonic() >= end:
            return None
        if stall > 600:
            S = rng.sample(range(G), d)
            cur = score(S)
            stall = 0
            continue
        i = rng.randrange(d)
        g = rng.randrange(G)
        if g in S:
            stall += 1
            continue
        T = S[:]
        T[i] = g
        s = score(T)
        if s < cur:
            stall = 0
        else:
            stall += 1
        if s <= cur:
            S, cur = T, s

    edges = []
    ps = [perms(g)[0] for g in S]
    for x in range(G):
        for P in ps:
            edges.append((x, G + P[x]))
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))

    if d <= 0 or D == 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Fallback: K_{d,d} has diameter 2, so it is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))

    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)
    G = max(d + 1, moore // 5)   # group order; vertex count is 2G <= moore
    found_any = False
    attempt_budget = 1.0

    while time.monotonic() < deadline and G <= moore // 2:
        cands = _groups_of_order(G)
        rng.shuffle(cands)
        success = None
        for cand in cands[:4]:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + attempt_budget)
            res = _search_group(cand[0], cand[1], cand[2], d, D, rng, end)
            if res is not None:
                n, edges = res
                if lib.is_valid(n, edges, d, D):
                    success = res
                    break

        if success is not None:
            n, edges = success
            if n > best[0]:
                best = (n, edges)
            found_any = True
            G += 1
        elif found_any:
            G += 1
        else:
            G = max(d + 1, G - max(1, G // 50))

    return best
