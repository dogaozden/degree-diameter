import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bipartite graph state with side-fixed double-edge switches.
#
# Every edge is stored as (a, b) with a on side A and b on side B. Each vertex
# keeps its side for the whole search, so a switch always produces A-B edges.
# A switch on edges (a,b), (c,e) yields (a,e), (c,b). Degrees are preserved.
# ----------------------------------------------------------------------------

class _State:
    def __init__(self, n, E):
        self.n = n
        self.E = [(int(a), int(b)) for a, b in E]
        self.nb = [[] for _ in range(n)]
        self.eset = set()
        for a, b in self.E:
            self.nb[a].append(b)
            self.nb[b].append(a)
            self.eset.add((a, b))

    def switch(self, i, j):
        """Double-edge switch on edge indices i and j. Returns False if it is illegal."""
        a, b = self.E[i]
        c, e = self.E[j]
        if a == c or b == e:
            return False
        if (a, e) in self.eset or (c, b) in self.eset:
            return False
        self.eset.discard((a, b))
        self.eset.discard((c, e))
        self.eset.add((a, e))
        self.eset.add((c, b))
        self.E[i] = (a, e)
        self.E[j] = (c, b)
        na = self.nb[a]
        na[na.index(b)] = e
        nbb = self.nb[b]
        nbb[nbb.index(a)] = c
        nc = self.nb[c]
        nc[nc.index(e)] = b
        ne = self.nb[e]
        ne[ne.index(c)] = a
        return True


def _bad_pairs(n, nb, D):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    total = 0
    for r in reach:
        total += n - r.bit_count()
    return total // 2


def _anneal(st, D, deadline, iters, rng):
    """Anneal switches to drive bad pairs to zero. Returns the final cost (0 = success)."""
    cost = _bad_pairs(st.n, st.nb, D)
    if cost == 0:
        return 0
    m = len(st.E)
    T0 = max(1.0, 0.1 * cost)
    T_end = 0.2
    decay = (T_end / T0) ** (1.0 / iters)
    T = T0
    for it in range(iters):
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        if not st.switch(i, j):
            continue
        c2 = _bad_pairs(st.n, st.nb, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost == 0:
                return 0
        else:
            st.switch(i, j)  # undo: the switch is its own inverse on these indices
    return cost


def _grow(st, d, rng):
    """Add one A vertex x and one B vertex y, each of degree d, by splicing out d edges.

    Pick d edges with pairwise distinct endpoints (a_i, b_i). Replace them with
    (x, b_i) and (a_i, y). Degrees of old vertices are unchanged, and the graph
    stays d-regular if it was d-regular before. Returns (n2, E2) or None.
    """
    n, E = st.n, st.E
    m = len(E)
    order = list(range(m))
    rng.shuffle(order)
    used_a, used_b, pick = set(), set(), []
    for i in order:
        a, b = E[i]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        pick.append(i)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    x, y = n, n + 1
    chosen = set(pick)
    newE = [E[k] for k in range(m) if k not in chosen]
    for i in pick:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    return n + 2, newE


def _search(seed_n, seed_E, d, D, deadline, rng):
    """Repeatedly grow by two vertices and anneal back to diameter <= D.

    The search always grows from the last valid graph. A failed attempt is
    discarded, and the next attempt uses a fresh random splice with a larger
    annealing budget.
    """
    best_n, best_E = seed_n, list(seed_E)
    fails = 0
    while time.monotonic() < deadline:
        base = _State(best_n, best_E)
        grown = _grow(base, d, rng)
        if grown is None:
            fails += 1
            if fails > 50:
                break
            continue
        n2, E2 = grown
        st = _State(n2, E2)
        iters = 600 + 200 * min(fails, 10)
        cost = _anneal(st, D, deadline, iters, rng)
        if cost == 0:
            best_n, best_E = n2, list(st.E)
            fails = 0
        else:
            fails += 1
    return best_n, best_E


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, which is d-regular with diameter 2.
    fb_n, fb_E = lib.haar_graph(d, range(d))
    fb_E = list(fb_E)
    if D == 2:
        return fb_n, fb_E

    # Projective plane incidence graph PG(2, d-1): d-regular, diameter 3.
    pg = None
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        pg_n, pg_E = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(pg_n, list(pg_E), d, D):
            pg = (pg_n, list(pg_E))

    if D == 3 and pg is not None:
        return pg

    if pg is not None:
        seed_n, seed_E = pg
    else:
        seed_n, seed_E = fb_n, fb_E

    rng = random.Random(seed * 1000003 + d * 101 + D)
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    bn, bE = _search(seed_n, seed_E, d, D, deadline, rng)

    candidates = [(seed_n, seed_E), (bn, bE), (fb_n, fb_E)]
    candidates.sort(key=lambda c: -c[0])
    for n, E in candidates:
        if lib.is_valid(n, E, d, D):
            return n, E
    return fb_n, fb_E
