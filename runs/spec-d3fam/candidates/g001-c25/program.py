"""Targets (D = 3): start from the best algebraic base (Araujo-Pardo-Lopez graph or PG(2,q)),
then grow it one vertex at a time. Each new vertex steals edge slots from saturated neighbours,
and a simulated-annealing repair of degree-preserving 2-switches restores diameter <= D.
Only zero-cost (valid) states are ever committed."""

import math
import random
import time

import lib

TIME_FRAC = 0.8        # fraction of time_limit used in total
GROW_STEPS = 300       # 2-switch annealing steps per attempted insertion
T_START = 1.0          # annealing temperature schedule (linear to T_END)
T_END = 0.05


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph."""
    adj = lib.adjacency(n, edges)
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


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def _edge_list(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


# ---------------------------------------------------------------- fast cost on set adjacency

def _bad_adj(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable counts), from set adjacency."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ---------------------------------------------------------------- new: steal-and-switch growth

def _fill(n, adj, color, d, rng):
    """Add edges between opposite-colour vertices that still have spare degree."""
    spare = [v for v in range(n) if len(adj[v]) < d]
    rng.shuffle(spare)
    for u in spare:
        if len(adj[u]) >= d:
            continue
        cands = [v for v in spare
                 if color[v] != color[u] and len(adj[v]) < d and v not in adj[u]]
        if cands:
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)


def _insert(n, adj, color, d, rng):
    """Add one vertex x of random colour c. Its d neighbours are opposite-colour vertices.
    Saturated neighbours give up one random edge (to a colour-c vertex), which frees a slot
    there. Returns the new vertex count."""
    c = rng.randrange(2)
    opp = [v for v in range(n) if color[v] != c]
    spare = [v for v in opp if len(adj[v]) < d]
    full = [v for v in opp if len(adj[v]) >= d]
    rng.shuffle(spare)
    rng.shuffle(full)
    chosen = (spare + full)[:d]
    x = n
    adj.append(set())
    color.append(c)
    n += 1
    for v in chosen:
        if len(adj[v]) >= d:
            w = rng.choice(tuple(adj[v]))
            adj[v].discard(w)
            adj[w].discard(v)
        adj[v].add(x)
        adj[x].add(v)
    return n


def _switch(adj, A, rng):
    """Random degree-preserving 2-switch between two colour-0 vertices a, c.
    Replaces (a,b),(c,dd) by (a,dd),(c,b). Returns an undo tuple, or None if not applicable."""
    a = A[rng.randrange(len(A))]
    if not adj[a]:
        return None
    b = rng.choice(tuple(adj[a]))
    c = A[rng.randrange(len(A))]
    if c == a or not adj[c]:
        return None
    dd = rng.choice(tuple(adj[c]))
    if dd == b or dd in adj[a] or b in adj[c]:
        return None
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(dd)
    adj[dd].discard(c)
    adj[a].add(dd)
    adj[dd].add(a)
    adj[c].add(b)
    adj[b].add(c)
    return (a, b, c, dd)


def _unswitch(adj, t):
    a, b, c, dd = t
    adj[a].discard(dd)
    adj[dd].discard(a)
    adj[c].discard(b)
    adj[b].discard(c)
    adj[a].add(b)
    adj[b].add(a)
    adj[c].add(dd)
    adj[dd].add(c)


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly insert a vertex, fill spare degree, then anneal 2-switches until the
    diameter is restored. Only zero-cost states are committed, so the result stays valid."""
    color = _two_colour(n, edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        A2 = [s.copy() for s in adj]
        C2 = list(color)
        n2 = _insert(n, A2, C2, d, rng)
        _fill(n2, A2, C2, d, rng)
        cur = _bad_adj(n2, A2, D)
        A0 = [v for v in range(n2) if C2[v] == 0]
        steps = 0
        while cur > 0 and steps < GROW_STEPS:
            if (steps & 31) == 0 and time.monotonic() > deadline:
                break
            steps += 1
            T = T_START + (T_END - T_START) * steps / GROW_STEPS
            t = _switch(A2, A0, rng)
            if t is None:
                continue
            new = _bad_adj(n2, A2, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                _unswitch(A2, t)
        if cur == 0:
            adj, color, n = A2, C2, n2
    return n, _edge_list(n, adj)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: always valid for D >= 2

    # Projective plane (diameter 3). Moore-extremal when d-1 is a prime power.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if D == 3 and lib.is_prime_power(d - 1):
                return _finish(cands + [base], d, D)
            cands.append(base)

    # Araujo-Pardo & Lopez record graph for d = q+2 with q = d-2 a prime power (D = 3).
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass

    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    if not valid:
        return lib.haar_graph(d, range(d))
    best = max(valid, key=lambda c: c[0])

    # Grow the largest valid base by steal-and-switch insertion for the remaining time.
    grown = _grow(best[0], best[1], d, D, rng, deadline)
    cands.append(grown)

    return _finish(cands, d, D)
