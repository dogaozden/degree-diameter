import math
import random
import time

import lib


def _kmat(d):
    """Degree matrix for a 2+2 base graph: row and column sums all equal d."""
    h, c = d // 2, (d + 1) // 2
    return [[c, h], [h, c]]


def _bad_sum(m, nb, nbase, D):
    """Total number of vertices at distance > D from (u, 0), summed over base vertices u.

    The lift is invariant under Z_m translation, so each base orbit has identical
    counts. This sum is therefore proportional to the number of bad pairs.
    Vertex id = base * m + g. nb[b] lists (w, shift) so that (b, g) ~ (w, g + shift).
    """
    n = nbase * m
    total = 0
    for u in range(nbase):
        src = u * m
        seen = {src}
        frontier = [src]
        for _ in range(D):
            new = []
            for key in frontier:
                b, g = divmod(key, m)
                for w, sh in nb[b]:
                    nk = w * m + (g + sh) % m
                    if nk not in seen:
                        seen.add(nk)
                        new.append(nk)
            frontier = new
            if not frontier:
                break
        total += n - len(seen)
    return total


def _search(m, s, t, K, D, rng, end):
    """Simulated annealing over Z_m voltages for a fixed s x t base multigraph.

    Dart counts K[i][j] are fixed. Voltages within one (i, j) pair are distinct,
    so the lift is simple. Returns the voltage table if bad == 0 before `end`,
    else None.
    """
    nbase = s + t

    def build_nb(volt):
        nb = [[] for _ in range(nbase)]
        for i in range(s):
            for j in range(t):
                for a in volt[i][j]:
                    nb[i].append((s + j, a))
                    nb[s + j].append((i, (-a) % m))
        return nb

    volt = [[rng.sample(range(m), K[i][j]) for j in range(t)] for i in range(s)]
    cur = _bad_sum(m, build_nb(volt), nbase, D)
    T = 0.6
    while cur > 0 and time.monotonic() < end:
        i = rng.randrange(s)
        j = rng.randrange(t)
        lst = volt[i][j]
        idx = rng.randrange(len(lst))
        new = rng.randrange(m)
        if new in lst:
            continue
        old = lst[idx]
        lst[idx] = new
        f = _bad_sum(m, build_nb(volt), nbase, D)
        if f <= cur or rng.random() < math.exp(-(f - cur) / T):
            cur = f
        else:
            lst[idx] = old
    if cur == 0:
        return volt
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(1.0, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Always-valid fallback: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))

    rng = random.Random(seed)
    s = t = 2
    K = _kmat(d)
    m = (d + 1) // 2 + 1
    budget = 3.0

    # Increase the cyclic order m one step at a time. Each success gives a lift
    # on 4m vertices. A failed attempt is retried with a doubled time budget.
    while time.monotonic() < end:
        now = time.monotonic()
        volt = _search(m, s, t, K, D, rng, min(end, now + budget))
        if volt is not None:
            edges = []
            for i in range(s):
                for j in range(t):
                    for a in volt[i][j]:
                        for g in range(m):
                            edges.append((i * m + g, (s + j) * m + (g + a) % m))
            n = (s + t) * m
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            m += 1
            budget = 3.0
        else:
            budget *= 2

    return best
