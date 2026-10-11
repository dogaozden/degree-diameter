"""Bi-Cayley lift search with a bitmask-ball objective and defect-driven repair.

New idea (not in the parent): instead of only accepting exact zero-defect lifts,
search a bi-Cayley lift on a slightly LARGER vertex set, accept it with a few
bad pairs, then shrink it to the target order by deleting the vertices that
carry the most bad pairs. Freed degree slots are refilled by greedy edge
additions chosen by exact bad-pair count. Adding edges never increases
distances, so the repair only has to remove the defects left by deletion.
"""
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bitballs(n, adj, D):
    """Bitmask per vertex of all vertices within distance D (dead vertices have no edges)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _bad_counts(n, adj, alive, D):
    """Return (total bad unordered pairs among alive vertices, per-vertex bad counts list)."""
    reach = _bitballs(n, adj, D)
    na = len(alive)
    per = [0] * n
    total = 0
    for v in alive:
        b = na - reach[v].bit_count()
        per[v] = b
        total += b
    return total // 2, per


def _group_choices(N):
    """Cyclic group Z_N plus small semidirect products Z_m x| Z_k with m*k = N."""
    out = [("cyc", N, 1, 0)]
    for k in (2, 3, 4):
        if N % k:
            continue
        m = N // k
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("sd", m, k, r))
    return out


def _group_mul(choice, N):
    kind, m, k, r = choice
    if kind == "cyc":
        return lambda x, y: (x + y) % N
    _, mul, _ = lib.semidirect_group(m, k, r)
    return mul


def _lift_adj(N, mul, S):
    """Bi-Cayley graph: A_x (index x) ~ B_{x*s} (index N + x*s) for s in S."""
    adj = [[] for _ in range(2 * N)]
    for x in range(N):
        for s in S:
            y = N + mul(x, s)
            adj[x].append(y)
            adj[y].append(x)
    return adj


def _climb(N, mul, d, D, rng, iters, deadline):
    """Hill-climb a connection set S minimising bad pairs; sideways moves allowed."""
    alive = list(range(2 * N))
    S = rng.sample(range(N), d)
    cur = _bad_counts(2 * N, _lift_adj(N, mul, S), alive, D)[0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _bad_counts(2 * N, _lift_adj(N, mul, S2), alive, D)[0]
        if v <= cur:
            S, cur = S2, v
    return S, cur


def _repair(n, adj, color, target, d, D, rng, deadline):
    """Delete the worst vertices down to `target`, then greedily add cross-side edges.

    adj: list of sets (mutated). Returns the alive set, or None on failure/timeout.
    """
    alive = set(range(n))
    while len(alive) > target:
        if time.monotonic() > deadline:
            return None
        _, per = _bad_counts(n, adj, alive, D)
        ranked = sorted(alive, key=lambda v: -per[v])
        v = rng.choice(ranked[:3])
        for u in adj[v]:
            adj[u].discard(v)
        adj[v].clear()
        alive.discard(v)

    total, _ = _bad_counts(n, adj, alive, D)
    while total > 0:
        if time.monotonic() > deadline:
            return None
        L = [v for v in alive if color[v] == 0 and len(adj[v]) < d]
        R = [v for v in alive if color[v] == 1 and len(adj[v]) < d]
        if not L or not R:
            return None
        pairs = [(a, b) for a in L for b in R if b not in adj[a]]
        if not pairs:
            return None
        cands = rng.sample(pairs, min(24, len(pairs)))
        best_t = None
        for a, b in cands:
            if time.monotonic() > deadline:
                return None
            adj[a].add(b)
            adj[b].add(a)
            t2, _ = _bad_counts(n, adj, alive, D)
            adj[a].discard(b)
            adj[b].discard(a)
            if best_t is None or t2 < best_t[0]:
                best_t = (t2, a, b)
        t2, a, b = best_t
        adj[a].add(b)
        adj[b].add(a)
        total = t2
    return alive


def _to_graph(adj, alive):
    order = sorted(alive)
    idx = {v: i for i, v in enumerate(order)}
    edges = [(idx[u], idx[v]) for u in order for v in adj[u] if u < v]
    return len(order), edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(res):
        nonlocal best
        if res is None:
            return
        n, e = res
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        consider(_best_pg(d))
        if best[0] >= moore:
            return best

    while best[0] < moore and time.monotonic() < deadline:
        target = best[0] + 2
        if target > moore:
            break
        # Lift side size N; the lift has 2N >= target vertices.
        N = (target + 1) // 2 + rng.randrange(0, 8)
        if d > N:
            continue
        choice = rng.choice(_group_choices(N))
        mul = _group_mul(choice, N)

        S, cur = _climb(N, mul, d, D, rng, 600, deadline)
        if cur == 0:
            # Zero-defect lift on 2N >= target vertices: accept directly.
            consider((2 * N, [(x, y) for x, y in _edges_of(N, mul, S)]))
            continue

        adj = [set(a) for a in _lift_adj(N, mul, S)]
        color = [0] * N + [1] * N
        alive = _repair(2 * N, adj, color, target, d, D, rng, deadline)
        if alive is not None:
            consider(_to_graph(adj, alive))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


def _edges_of(N, mul, S):
    """Edge list of the bi-Cayley lift (A_x, N + x*s), with A-indices first."""
    E = []
    for x in range(N):
        for s in S:
            E.append((x, N + mul(x, s)))
    return E
