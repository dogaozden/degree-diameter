import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite group lifts with two base vertices.
#
# Left vertex x (index x) is joined to right vertex x*g (index G + x*g) for each
# g in S, where G is a finite group of order `order`. The group acts on both
# sides by left multiplication and transitively on each side, so the diameter
# is at most D exactly when BFS from left identity and from right identity
# reach every vertex within distance D.
# ----------------------------------------------------------------------------

def _specs(G, rng):
    """Semidirect products Z_m x| Z_k with m*k = G, as (m, k, r) triples."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:40]


class _Ctx:
    def __init__(self, spec):
        m, k, r = spec
        self.order, self.mul, self.inv = lib.semidirect_group(m, k, r)
        self._cache = {}
        self.invs = [self.inv(g) for g in range(self.order)]

    def col(self, g):
        c = self._cache.get(g)
        if c is None:
            mul = self.mul
            c = [mul(x, g) for x in range(self.order)]
            self._cache[g] = c
        return c


def _cost(ctx, S, D):
    """Number of (source, vertex) pairs at distance > D from left 0 and from right 0."""
    G = ctx.order
    cl = [ctx.col(g) for g in S]
    cr = [ctx.col(ctx.invs[g]) for g in S]
    total = 0
    for src in (0, G):
        dist = [-1] * (2 * G)
        dist[src] = 0
        frontier = [src]
        for depth in range(1, D + 1):
            nxt = []
            for v in frontier:
                if v < G:
                    nb = [G + c[v] for c in cl]
                else:
                    y = v - G
                    nb = [c[y] for c in cr]
                for w in nb:
                    if dist[w] < 0:
                        dist[w] = depth
                        nxt.append(w)
            frontier = nxt
            if not frontier:
                break
        total += sum(1 for t in dist if t < 0)
    return total


def _hill(ctx, d, D, iters, rng, t_end):
    """Local search over d-subsets S of the group; returns S with zero cost, or None."""
    G = ctx.order
    S = rng.sample(range(G), d)
    c = _cost(ctx, S, D)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 15) == 0 and time.monotonic() >= t_end:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c2 = _cost(ctx, T, D)
        if c2 <= c or rng.random() < 0.03:
            S, c = T, c2
    return S if c == 0 else None


def _search_order(G, d, D, rng, t_end, ctx_cache):
    """Try to find a valid lift over a group of order G before t_end."""
    if d > G:
        return None
    specs = _specs(G, rng)
    if not specs:
        return None
    i = 0
    while time.monotonic() < t_end:
        spec = specs[i % len(specs)]
        i += 1
        ctx = ctx_cache.get(spec)
        if ctx is None:
            ctx = _Ctx(spec)
            ctx_cache[spec] = ctx
        S = _hill(ctx, d, D, 400, rng, t_end)
        if S is not None:
            return ctx, S
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Upward scan over group orders G: a lift over G has 2G vertices.
    G = max(d, best[0] // 2 + 1)
    ctx_cache = {}
    while G <= moore // 2 and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        t_end = min(deadline, now + max(0.2, 0.06 * remaining))
        res = _search_order(G, d, D, rng, t_end, ctx_cache)
        if res is not None:
            ctx, S = res
            edges = lib.group_lift(2, [(0, 1, g) for g in S], ctx.order, ctx.mul)[1]
            consider(2 * ctx.order, edges)
        G += 1

    return best
