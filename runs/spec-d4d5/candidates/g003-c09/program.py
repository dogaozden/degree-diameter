import math
import random
import time

import lib


BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Basic graph utilities (adjacency lists, bitmask balls).
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _edges_from_adj(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _adj_from_edges(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over small semidirect products (initial seeds).
# ----------------------------------------------------------------------------

def _group_table(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (G, multiplication table)."""
    for _ in range(40):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6])
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
        table = [[mul(g, s) for s in range(order)] for g in range(order)]
        return order, table
    return None


def _lift_candidate(d, D, k, G, table, rng, deadline, iters):
    """Hill-climb the voltages of a bi-Cayley lift with k+k vertices-blocks of size G.

    Dart (i, j, s) joins A_{i,g} to B_{j, g*s}. Each A-block vertex gets d darts.
    Returns (n, edges) of a valid-diameter lift, or None.
    """
    N = 2 * k * G
    need = k * G * d
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    def graph():
        E = set()
        for i, j, s in darts:
            ba = i * G
            bb = (k + j) * G
            for g in range(G):
                E.add((ba + g, bb + table[g][s]))
        return E

    def cost():
        E = graph()
        if len(E) < need:
            return BIG
        adj = _adj_from_edges(N, E)
        return _bad_pairs(N, adj, D)

    c = cost()
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        darts[idx][2] = rng.randrange(G)
        c2 = cost()
        if c2 <= c:
            c = c2
        else:
            darts[idx][2] = old
    if c != 0:
        return None
    return N, sorted(graph())


# ----------------------------------------------------------------------------
# Bold new search: local search over bipartite graphs with a fixed vertex set.
#
# State: a bipartite graph with max degree d on n vertices (sides 0 and 1).
# Moves: degree-preserving 2-switches, adding an edge between deficient
# opposite vertices, and "steal" moves that attach a deficient vertex to a
# vertex on the other side by removing one of that vertex's edges.
# Cost: bad pairs + 0.5 * total degree deficit. Simulated annealing.
# Growth adds one vertex at a time to a valid graph and repairs it.
# ----------------------------------------------------------------------------

def _propose(n, adj, side, A, B, d, rng):
    r = rng.random()
    if r < 0.5:
        if len(A) < 2:
            return None
        a = rng.choice(A)
        c = rng.choice(A)
        if c == a or not adj[a] or not adj[c]:
            return None
        b = rng.choice(adj[a])
        e = rng.choice(adj[c])
        if e == b or e in adj[a] or b in adj[c]:
            return None
        return [('r', a, b), ('r', c, e), ('a', a, e), ('a', c, b)]
    if r < 0.8:
        defA = [u for u in A if len(adj[u]) < d]
        defB = [v for v in B if len(adj[v]) < d]
        if not defA or not defB:
            return None
        u = rng.choice(defA)
        v = rng.choice(defB)
        if v in adj[u]:
            return None
        return [('a', u, v)]
    defs = [x for x in range(n) if len(adj[x]) < d]
    if not defs:
        return None
    x = rng.choice(defs)
    pool = B if side[x] == 0 else A
    y = rng.choice(pool)
    if y in adj[x] or not adj[y]:
        return None
    z = rng.choice(adj[y])
    return [('r', z, y), ('a', x, y)]


def _apply(adj, ops):
    for kind, u, v in ops:
        if kind == 'a':
            adj[u].append(v)
            adj[v].append(u)
        else:
            adj[u].remove(v)
            adj[v].remove(u)


def _inverse(ops):
    return [('r' if kind == 'a' else 'a', u, v) for kind, u, v in reversed(ops)]


def _anneal(n, adj, side, d, D, deadline, rng):
    """Repair the graph until its diameter is at most D. Returns True on success."""
    A = [v for v in range(n) if side[v] == 0]
    B = [v for v in range(n) if side[v] == 1]

    def score():
        bad = _bad_pairs(n, adj, D)
        defi = sum(d - len(a) for a in adj)
        return bad, defi

    bad, defi = score()
    cur = bad + 0.5 * defi
    T = 0.4
    it = 0
    while True:
        if bad == 0:
            return True
        if (it & 7) == 0 and time.monotonic() >= deadline:
            return False
        it += 1
        ops = _propose(n, adj, side, A, B, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        bad2, defi2 = score()
        new = bad2 + 0.5 * defi2
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            bad = bad2
        else:
            _apply(adj, _inverse(ops))


def _grow(n, edges, d, D, deadline, rng):
    """Add one vertex at a time, repairing with annealing. Returns the largest valid (n, edges)."""
    adj = _adj_from_edges(n, edges)
    side = _bipartition(n, adj)
    best = (n, list(edges))
    while time.monotonic() < deadline:
        cnt0 = side.count(0)
        s = 0 if cnt0 <= n - cnt0 else 1
        adj.append([])
        side.append(s)
        n += 1
        if not _anneal(n, adj, side, d, D, deadline, rng):
            break
        best = (n, _edges_from_adj(adj))
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _lift_until(d, D, st, rng, until, update):
    while time.monotonic() < until:
        k = rng.choice([1, 2, 2, 3])
        target = st[0] + 2 + rng.randrange(0, 3)
        G = max(2, target // (2 * k)) + rng.randrange(0, 2)
        g = _group_table(G, rng)
        if g is None:
            continue
        order, table = g
        res = _lift_candidate(d, D, k, order, table, rng, until, 300)
        if res is not None:
            update(res[0], res[1])


def _search(d, D, rng, start, budget, st, update):
    B = budget
    deadline = start + B
    _lift_until(d, D, st, rng, min(deadline, start + 0.4 * B), update)
    while time.monotonic() < deadline:
        grow_until = min(deadline, time.monotonic() + 0.2 * B)
        n, e = _grow(st[0], st[1], d, D, grow_until, rng)
        update(n, e)
        if time.monotonic() < deadline:
            _lift_until(d, D, st, rng,
                        min(deadline, time.monotonic() + 0.1 * B), update)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    st = [fb_n, fb_e]

    def update(n, e):
        if n > st[0] and lib.is_valid(n, e, d, D):
            st[0] = n
            st[1] = e

    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            update(pg[0], pg[1])

    try:
        if d >= 2 and D >= 2:
            _search(d, D, rng, start, budget, st, update)
    except Exception:
        pass

    if lib.is_valid(st[0], st[1], d, D):
        return st[0], st[1]
    fb_n, fb_e = lib.haar_graph(d, range(d))
    return fb_n, fb_e
