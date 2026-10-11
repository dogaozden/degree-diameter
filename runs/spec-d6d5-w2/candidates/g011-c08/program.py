import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups Z_m x|_r Z_k2, found by annealing.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k + j)*G + h, with g, h in the group.
# A block (i, j) holds a set S_ij of right multipliers. The edges are
# A_{i,g} -- B_{j, g*s} for every s in S_ij. Row and column sums of block sizes
# equal d, so every vertex has degree d. Left multiplication by the group is an
# automorphism, so vertex 0 of each class represents its whole class. Diameter
# <= D therefore holds iff those 2k BFS sources reach everything within D steps.
# This family differs from the parent's voltage lifts: it is a single-orbit
# bi-Cayley search over many non-cyclic groups with a larger order ladder.
# ----------------------------------------------------------------------------

_GOPT = {}


def _group_opts(G):
    """All (m, k2, r) with Z_m x|_r Z_k2 of order G (r = 1 gives the direct product)."""
    if G in _GOPT:
        return _GOPT[G]
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
    _GOPT[G] = opts
    return opts


def _pick_group(G, rng):
    opts = _group_opts(G)
    if not opts:
        return None
    nonab = [o for o in opts if o[1] > 1 and o[2] != 1]
    if nonab and rng.random() < 0.75:
        return rng.choice(nonab)
    return rng.choice(opts)


def _cost(k, G, D, S, rp, limit):
    """Total number of vertices not reached within D from the 2k representatives."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i in range(k):
        ai = i * G
        for j in range(k):
            bj = (k + j) * G
            for s in S[i][j]:
                p = rp(s)
                for g in range(G):
                    a = ai + g
                    b = bj + p[g]
                    adj[a].append(b)
                    adj[b].append(a)
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in srcs:
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
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
        if total > limit:
            return total
    return total


def _edges(k, G, S, rp):
    E = []
    for i in range(k):
        for j in range(k):
            for s in S[i][j]:
                p = rp(s)
                for g in range(G):
                    E.append((i * G + g, (k + j) * G + p[g]))
    return 2 * k * G, E


def _sa(d, D, k, G, rp, rng, t_end, max_iters):
    """Anneal the multiplier sets. Returns (n, edges) on success, else None."""
    if k == 1:
        C = [[d]]
    else:
        x = rng.randint(1, d - 1)
        C = [[x, d - x], [d - x, x]]
    S = [[rng.sample(range(G), C[i][j]) if C[i][j] else [] for j in range(k)]
         for i in range(k)]
    blocks = [(i, j) for i in range(k) for j in range(k) if C[i][j] > 0]
    cur = _cost(k, G, D, S, rp, float("inf"))
    T = 1.5
    for it in range(max_iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() >= t_end:
            break
        i, j = rng.choice(blocks)
        lst = S[i][j]
        t = rng.randrange(len(lst))
        old = lst[t]
        new = rng.randrange(G)
        while new in lst:
            new = rng.randrange(G)
        lst[t] = new
        limit = cur - T * math.log(1.0 - rng.random())
        c2 = _cost(k, G, D, S, rp, limit)
        if c2 <= limit:
            cur = c2
        else:
            lst[t] = old
        T = max(0.05, T * 0.998)
    if cur == 0:
        return _edges(k, G, S, rp)
    return None


def _attempt(d, D, k, G, t_end, rng):
    """Try random groups of order G until one yields a valid lift or time runs out."""
    while time.monotonic() < t_end:
        opt = _pick_group(G, rng)
        if opt is None:
            return None
        m, k2, r = opt
        _, mul, _ = lib.semidirect_group(m, k2, r)
        cache = {}

        def rp(s, cache=cache, mul=mul, G=G):
            p = cache.get(s)
            if p is None:
                p = [mul(g, s) for g in range(G)]
                cache[s] = p
            return p

        res = _sa(d, D, k, G, rp, rng, t_end, 3000)
        if res is not None:
            return res
    return None


def _generic_search(d, D, deadline, rng, best):
    """Climb the order ladder: keep trying larger bi-Cayley orders over k = 1 and k = 2."""
    step = {1: 8, 2: 4}
    fails = {1: 0, 2: 0}
    while time.monotonic() < deadline - 0.5:
        ks = [k for k in (1, 2) if fails[k] < 5]
        if not ks:
            break
        k = rng.choice(ks)
        G = best[0] // (2 * k) + step[k]
        t_end = min(deadline, time.monotonic() + 6.0)
        res = _attempt(d, D, k, G, t_end, rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
            step[k] = min(step[k] * 2, 64)
            fails[k] = 0
        else:
            fails[k] += 1
            step[k] = max(1, step[k] // 2)
    return best


# ----------------------------------------------------------------------------
# Small classical families (used for D = 2, 3 and as fallbacks).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    K = [(i, d + j) for i in range(d) for j in range(d)]
    best = (2 * d, K)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if d == 2:
            n = 2 * D
            consider(n, [(i, (i + 1) % n) for i in range(n)])
        if D == 3:
            pg = _pg_candidate(d)
            if pg is not None:
                consider(pg[0], pg[1])
            if d >= 5 and lib.is_prime_power(d - 2) and d - 2 >= 3:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
    except Exception:
        pass

    # Main bold search for D >= 4: non-cyclic bi-Cayley lifts with a growing order ladder.
    if D >= 4 and d >= 3 and time.monotonic() < deadline:
        try:
            best = _generic_search(d, D, deadline, rng, best)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, K)
    return best
