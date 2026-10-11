import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of algebraic bases and voltage lifts, this program runs
# simulated annealing directly on d-regular bipartite graphs. Moves are
# degree-preserving double edge switches; the cost is the exact number of vertex
# pairs at distance > D. The order is grown one vertex per side at a time, and
# each level is annealed to cost zero. K_{d,d} is the always-valid fallback.
# ----------------------------------------------------------------------------

TIME_FRAC = 0.80
ANNEAL_ITERS = 4000
T_START = 3.0
T_END = 0.2


class _Graph:
    """d-regular bipartite multigraph-free graph; vertex ids are 0..N-1 and side[v] is 0 or 1."""

    def __init__(self, d):
        self.d = d
        self.side = [0] * d + [1] * d
        self.adj = ([list(range(d, 2 * d)) for _ in range(d)]
                    + [list(range(d)) for _ in range(d)])
        self.A = list(range(d))
        self.B = list(range(d, 2 * d))


def _expand(g, rng):
    """Add one vertex to each side, keeping the graph d-regular and bipartite.

    Pick d A-vertices a_i with distinct neighbours b_i. Replace edge a_i-b_i by
    a_i-b_new and a_new-b_i, and add the new vertices a_new and b_new.
    """
    d = g.d
    while True:
        As = rng.sample(g.A, d)
        used = set()
        bs = []
        ok = True
        for a in As:
            choices = [b for b in g.adj[a] if b not in used]
            if not choices:
                ok = False
                break
            b = rng.choice(choices)
            used.add(b)
            bs.append(b)
        if ok:
            break
    a_new = len(g.side)
    b_new = a_new + 1
    g.side += [0, 1]
    g.adj += [[], []]
    for a, b in zip(As, bs):
        la = g.adj[a]
        la[la.index(b)] = b_new
        lb = g.adj[b]
        lb[lb.index(a)] = a_new
        g.adj[a_new].append(b)
        g.adj[b_new].append(a)
    g.A.append(a_new)
    g.B.append(b_new)


def _switch(g, rng):
    """Double edge switch a1-b1, a2-b2 -> a1-b2, a2-b1. Returns an undo token or None."""
    a1 = rng.choice(g.A)
    a2 = rng.choice(g.A)
    if a1 == a2:
        return None
    i = rng.randrange(len(g.adj[a1]))
    j = rng.randrange(len(g.adj[a2]))
    b1 = g.adj[a1][i]
    b2 = g.adj[a2][j]
    if b1 == b2 or b2 in g.adj[a1] or b1 in g.adj[a2]:
        return None
    g.adj[a1][i] = b2
    g.adj[a2][j] = b1
    l = g.adj[b1]
    l[l.index(a1)] = a2
    l = g.adj[b2]
    l[l.index(a2)] = a1
    return (a1, i, a2, j, b1, b2)


def _undo(g, mv):
    a1, i, a2, j, b1, b2 = mv
    g.adj[a1][i] = b1
    g.adj[a2][j] = b2
    l = g.adj[b1]
    l[l.index(a2)] = a1
    l = g.adj[b2]
    l[l.index(a1)] = a2


def _bad(g, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    adj = g.adj
    N = len(adj)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            reach = new
            break
        reach = new
    tot = 0
    for r in reach:
        tot += N - r.bit_count()
    return tot // 2


def _anneal(g, D, iters, rng, deadline):
    """Simulated annealing on double switches; returns the final cost (0 means valid)."""
    cost = _bad(g, D)
    if cost == 0:
        return 0
    for t in range(iters):
        if time.monotonic() > deadline:
            break
        T = T_START * (T_END / T_START) ** (t / max(1, iters))
        mv = _switch(g, rng)
        if mv is None:
            continue
        c2 = _bad(g, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                break
        else:
            _undo(g, mv)
    return cost


def _edge_list(g):
    E = []
    for u in range(len(g.adj)):
        for v in g.adj[u]:
            if u < v:
                E.append((u, v))
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRAC * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D  # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d}: diameter 2, always valid.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if D == 2:
        return fb_n, fb_e

    # Projective-plane incidence graph is Moore-optimal for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    best = (fb_n, fb_e)
    moore = lib._moore_bound(d, D)

    try:
        g = _Graph(d)
        k0 = max(d + 1, int(0.4 * moore / 2))
        while len(g.A) < k0:
            _expand(g, rng)

        while time.monotonic() < deadline:
            cost = _anneal(g, D, ANNEAL_ITERS, rng, deadline)
            if cost == 0:
                n = len(g.side)
                if n > best[0]:
                    e = _edge_list(g)
                    if lib.is_valid(n, e, d, D):
                        best = (n, e)
                if n >= moore or time.monotonic() > deadline:
                    break
                _expand(g, rng)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fb_n, fb_e
    return best
