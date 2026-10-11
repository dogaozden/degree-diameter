"""Bipartite degree/diameter search, rewritten around degree-preserving 2-switch annealing.

Scope of this version: the weakest scored target (d=6, D=5) gets a new family.
Instead of searching voltage or bi-Cayley lifts, it starts from a plain Haar
graph (a d-regular bipartite circulant, always valid) at a chosen order
2h, then runs simulated annealing over degree-preserving 2-switches, with the
number of unreached vertex pairs within distance D as the cost. When an
attempt fails, far-off vertices are deleted in batches to recover a valid
smaller graph. Every candidate is checked with lib.is_valid before it is kept,
so the returned graph is always valid. The fallback is K_{d,d}, or the
projective-plane / Araujo-Pardo-Lopez graphs for D = 3.

Expected effect: this is an unproven, high-risk change. It may or may not
reach or beat the record 684 for d=6, D=5 within the time budget.
"""
import math
import random
import time

import lib


def _balls(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _cost(n, adj, D):
    """Number of unordered-or-ordered vertex pairs not within distance D (zero means valid)."""
    return sum(n - b.bit_count() for b in _balls(n, adj, D))


def _haar_start(h, d, rng):
    """d-regular simple bipartite graph on h+h vertices: left i ~ right (i+s) mod h for s in S."""
    S = rng.sample(range(h), d)
    return [[i, h + (i + s) % h] for i in range(h) for s in S]


def _anneal(h, d, D, E, deadline, rng):
    """Degree-preserving 2-switch annealing on left 0..h-1, right h..2h-1.

    Returns (success, adj) where adj is a list of sets for the final graph.
    """
    n = 2 * h
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    cur = _cost(n, adj, D)
    m = len(E)
    t0, t1 = 2.0, 0.05
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline or m < 2:
            break
        T = t0 * (t1 / t0) ** min(1.0, (now - t_start) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        # Replace (a,b),(c,e) with (a,e),(c,b). a,c are left; b,e are right.
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(n, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0, adj


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    while time.monotonic() < deadline:
        if n == 0:
            return None
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        balls = _balls(n, adj, D)
        bad = [n - b.bit_count() for b in balls]
        if not any(bad):
            return n, edges
        order = [v for v in range(n) if bad[v] > 0]
        rng.shuffle(order)
        order.sort(key=lambda v: -bad[v])
        k = max(1, len(order) // 12)
        dead = set(order[:k])
        new = {}
        for v in range(n):
            if v not in dead:
                new[v] = len(new)
        edges = [(new[u], new[v]) for u, v in edges if u in new and v in new]
        n = len(new)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D == 3:
        if lib.is_prime_power(d - 1) and d - 1 >= 2:
            consider(*lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if best_n > 2 * (d * d - d + 1) - 1:
            return best

    # Main family: annealed Haar starts at increasing order, with repair fallback.
    moore = lib.moore_bound(d, D)
    h = max(d, int(0.42 * moore / 2), best_n // 2 + 1)
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        slice_ = min(remaining, max(4.0, 0.35 * remaining))
        E = _haar_start(h, d, rng)
        ok, adj = _anneal(h, d, D, E, time.monotonic() + slice_, rng)
        edges = [(a, b) for a in range(h) for b in adj[a]]
        if ok:
            consider(2 * h, edges)
            h += 1
        else:
            rep_deadline = min(deadline, time.monotonic() + max(2.0, 0.5 * slice_))
            rep = _repair(2 * h, edges, D, rep_deadline, rng)
            if rep is not None:
                consider(rep[0], rep[1])
                h = max(h, best_n // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
