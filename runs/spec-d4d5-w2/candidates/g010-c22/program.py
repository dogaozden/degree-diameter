import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Edge-switching annealer on a bipartite graph with fixed vertex count.
#
# State: a bipartite graph (side fixed per vertex) with max degree d.
# Cost = (ordered pairs at distance > D) + (total degree deficiency).
# Moves: degree-preserving 2-switches, and "fill" moves that attach a
# deficient vertex to a free or stealable opposite-side vertex.
# Growth adds one vertex per side and anneals to zero bad pairs.
# ----------------------------------------------------------------------------

G_ITERS = 3000
G_REP = 1500
KICK = 8


def _bad_ordered(n, adj, D):
    """Number of ordered vertex pairs at distance > D (unreachable counts)."""
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


def _deficit(adj, d):
    return sum(d - len(a) for a in adj)


def _apply(adj, ops):
    for kind, u, v in ops:
        if kind:
            adj[u].add(v)
            adj[v].add(u)
        else:
            adj[u].discard(v)
            adj[v].discard(u)


def _undo(adj, ops):
    for kind, u, v in reversed(ops):
        if kind:
            adj[u].discard(v)
            adj[v].discard(u)
        else:
            adj[u].add(v)
            adj[v].add(u)


def _switch(adj, lefts, rng):
    """Degree-preserving double edge swap; returns ops or []."""
    if len(lefts) < 2:
        return []
    a1, a2 = rng.sample(lefts, 2)
    if not adj[a1] or not adj[a2]:
        return []
    b1 = rng.choice(tuple(adj[a1]))
    b2 = rng.choice(tuple(adj[a2]))
    if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return []
    return [(0, a1, b1), (0, a2, b2), (1, a1, b2), (1, a2, b1)]


def _fill(adj, side, n, d, lefts, rights, rng):
    """Attach a deficient vertex to an opposite vertex, stealing an edge if needed."""
    deficient = [v for v in range(n) if len(adj[v]) < d]
    if not deficient:
        return []
    x = rng.choice(deficient)
    opp = rights if side[x] == 0 else lefts
    free = [y for y in opp if len(adj[y]) < d and y not in adj[x]]
    if free:
        y = rng.choice(free)
        return [(1, x, y)]
    full = [y for y in opp if y not in adj[x] and adj[y]]
    if not full:
        return []
    y = rng.choice(full)
    z = rng.choice(tuple(adj[y]))
    return [(0, y, z), (1, x, y)]


def _anneal(n, side, adj, d, D, deadline, rng, iters, T0=3.0, T1=0.15):
    """Anneal adj in place toward zero bad pairs. Returns True on success."""
    bad = _bad_ordered(n, adj, D)
    if bad == 0:
        return True
    lefts = [v for v in range(n) if side[v] == 0]
    rights = [v for v in range(n) if side[v] == 1]
    cost = bad + _deficit(adj, d)
    ratio = T1 / T0
    for it in range(iters):
        if (it & 15) == 0 and time.monotonic() > deadline:
            return False
        T = T0 * ratio ** (it / iters)
        if rng.random() < 0.6:
            ops = _switch(adj, lefts, rng)
        else:
            ops = _fill(adj, side, n, d, lefts, rights, rng)
        if not ops:
            continue
        _apply(adj, ops)
        nb = _bad_ordered(n, adj, D)
        nc = nb + _deficit(adj, d)
        delta = nc - cost
        if nb == 0 or delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = nc
            if nb == 0:
                return True
        else:
            _undo(adj, ops)
    return False


# ----------------------------------------------------------------------------
# Haar-graph seed (quick hill-climb on the connection set).
# ----------------------------------------------------------------------------

def _haar_search(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(T):
        n, e = lib.haar_graph(m, T)
        return lib.bad_pairs(n, e, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() > deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _haar_seed(d, D, cap, rng, deadline):
    m = max(d + 2, cap // 4)
    found = None
    while m >= d + 2 and time.monotonic() < deadline:
        S = _haar_search(d, D, m, rng, deadline, 150)
        if S is not None:
            found = (m, S)
            break
        m -= 3
    if found is None:
        return None
    m, S = found
    best = lib.haar_graph(m, S)
    m += 1
    while time.monotonic() < deadline:
        S = _haar_search(d, D, m, rng, deadline, 150)
        if S is None:
            break
        best = lib.haar_graph(m, S)
        m += 1
    return best


# ----------------------------------------------------------------------------
# Helpers for state conversion.
# ----------------------------------------------------------------------------

def _sides(n):
    return [0 if v < n // 2 else 1 for v in range(n)]


def _adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _k_dd(d):
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.8 * time_limit - 1.0)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if D == 2:
        return _k_dd(d)
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    cap = lib.moore_bound(d, D)
    best_n, best_e = _k_dd(d)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
    if q is not None:
        n, e = lib.projective_plane_incidence(q)
        consider(n, e)

    if best_n < cap:
        hs = _haar_seed(d, D, cap, rng, start + 0.2 * budget)
        if hs is not None:
            consider(hs[0], hs[1])

    if best_n >= cap:
        return best_n, best_e

    cur_n = best_n
    cur_e = best_e
    cur_side = _sides(cur_n)
    cur_adj = _adj(cur_n, cur_e)

    while time.monotonic() < deadline and best_n < cap:
        # Attempt to grow by one vertex per side.
        adj2 = [set(s) for s in cur_adj] + [set(), set()]
        side2 = cur_side + [0, 1]
        if _anneal(cur_n + 2, side2, adj2, d, D, deadline, rng, G_ITERS):
            cur_n += 2
            cur_side = side2
            cur_adj = adj2
            consider(cur_n, _edges(cur_n, cur_adj))
            continue

        # Plateau walk: kick the valid graph and repair at the same order.
        adj3 = [set(s) for s in cur_adj]
        lefts = [v for v in range(cur_n) if cur_side[v] == 0]
        for _ in range(KICK):
            ops = _switch(adj3, lefts, rng)
            if ops:
                _apply(adj3, ops)
        if _anneal(cur_n, cur_side, adj3, d, D, deadline, rng, G_REP):
            cur_adj = adj3

    if not lib.is_valid(best_n, best_e, d, D):
        return _k_dd(d)
    return best_n, best_e
