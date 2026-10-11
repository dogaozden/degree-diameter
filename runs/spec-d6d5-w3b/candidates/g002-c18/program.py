import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: random 6-regular-style bipartite graphs repaired by edge switches.
#
# Instead of algebraic voltage lifts, this search works directly on bipartite
# graphs with degree d on both sides:
#   1. Start from K_{d,d} (valid for D = 2).
#   2. Grow by one A-vertex and one B-vertex. Each new vertex takes d-1 "edge
#      insertions" (replace edge (x,y) by (x,b) and (a,y)), which keeps every
#      degree at d.
#   3. Anneal with degree-preserving edge switches, minimising the number of
#      ordered vertex pairs at distance > D (bitset BFS).
#   4. Keep a grown graph only when the cost reaches zero; otherwise revert.
#
# Safe fallbacks: K_{d,d} (or C_{2D} for d = 2, K_2 for D = 1) and the
# projective-plane / Araujo-Pardo-Lopez constructions when they apply. Every
# candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------


def _bad_pairs_ordered(n, adj, D):
    """Ordered pairs at distance > D (bit-parallel BFS). Zero iff diameter <= D and connected."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


class _Bip:
    """Bipartite graph with sides A (local ids 0..s-1) and B (local ids 0..s-1)."""

    def __init__(self, d, s):
        self.d = d
        self.s = s
        self.E = []
        self.S = set()
        self.adjA = [[] for _ in range(s)]
        self.adjB = [[] for _ in range(s)]

    def add_edge(self, a, b):
        self.E.append((a, b))
        self.S.add((a, b))
        self.adjA[a].append(b)
        self.adjB[b].append(a)

    def set_edge(self, i, a, b):
        oa, ob = self.E[i]
        self.S.discard((oa, ob))
        self.adjA[oa].remove(ob)
        self.adjB[ob].remove(oa)
        self.E[i] = (a, b)
        self.S.add((a, b))
        self.adjA[a].append(b)
        self.adjB[b].append(a)

    def clone(self):
        c = _Bip(self.d, self.s)
        c.E = list(self.E)
        c.S = set(self.S)
        c.adjA = [list(x) for x in self.adjA]
        c.adjB = [list(x) for x in self.adjB]
        return c

    def adj(self):
        # Global ids: A vertex a -> a, B vertex b -> s + b.
        s = self.s
        out = [[s + b for b in lst] for lst in self.adjA]
        out.extend(self.adjB)
        return out

    def cost(self, D):
        return _bad_pairs_ordered(2 * self.s, self.adj(), D)

    def edges(self):
        s = self.s
        return [(a, s + b) for a, b in self.E]


def _grow_once(g, rng):
    """Add one A vertex and one B vertex, both of degree d, by edge insertions. Returns False on failure."""
    d = g.d
    a = g.s
    b = g.s
    g.s += 1
    g.adjA.append([])
    g.adjB.append([])
    g.add_edge(a, b)
    for _ in range(d - 1):
        done = False
        m = len(g.E)
        for _t in range(4000):
            i = rng.randrange(m)
            x, y = g.E[i]
            if x == a or y == b or x in g.adjB[b] or y in g.adjA[a]:
                continue
            g.set_edge(i, x, b)   # (x,y) -> (x,b)
            g.add_edge(a, y)      # plus (a,y); degrees of x, y unchanged
            done = True
            break
        if not done:
            return False
    return True


def _anneal(g, D, deadline, iters, rng):
    """Degree-preserving edge switches that drive the bad-pair count to zero. Returns final cost."""
    cur = g.cost(D)
    m = len(g.E)
    T = 1.5
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(0.2, T * 0.99)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = g.E[i]
        a2, b2 = g.E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in g.S or (a2, b1) in g.S:
            continue
        g.set_edge(i, a1, b2)
        g.set_edge(j, a2, b1)
        new = g.cost(D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            g.set_edge(j, a2, b2)
            g.set_edge(i, a1, b1)
    return cur


def _search(d, D, deadline, rng, consider):
    """Grow a valid bipartite graph of degree d and diameter <= D one vertex pair at a time."""
    cur = _Bip(d, d)
    for a in range(d):
        for b in range(d):
            cur.add_edge(a, b)
    budget = 80
    fails = 0
    grow_fails = 0
    while time.monotonic() < deadline:
        trial = cur.clone()
        if not _grow_once(trial, rng):
            grow_fails += 1
            if grow_fails > 20:
                break
            continue
        c = _anneal(trial, D, deadline, budget, rng)
        if c == 0:
            cur = trial
            consider(2 * cur.s, cur.edges())
            budget = max(40, budget // 2)
            fails = 0
        else:
            budget = min(4000, budget * 2)
            fails += 1
            if fails > 12 and budget >= 4000:
                break


def _make_consider(d, D, best):
    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
    return consider


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    kn = lib.haar_graph(d, range(d))
    best = [kn[0], kn[1]]
    if D == 2:
        return best[0], best[1]

    consider = _make_consider(d, D, best)

    # Algebraic baselines (diameter 3 constructions are valid for every D >= 3).
    q = d - 1
    if lib.is_prime_power(q):
        n1, e1 = lib.projective_plane_incidence(q)
        consider(n1, e1)
        if D == 3:
            return best[0], best[1]
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n2, e2 = lib.araujo_lopez_graph(d - 2)
            consider(n2, e2)
        except Exception:
            pass

    # Main search: grow random-like bipartite graphs and repair by edge switches.
    time_budget = min(0.85 * time_limit, time_limit - 2.5)
    deadline = start + max(0.5, time_budget)
    rng = random.Random(seed * 1000003 + d * 101 + D)
    try:
        _search(d, D, deadline, rng, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        kn = lib.haar_graph(d, range(d))
        return kn[0], kn[1]
    return best[0], best[1]
