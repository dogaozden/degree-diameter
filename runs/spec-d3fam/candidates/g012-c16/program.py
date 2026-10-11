import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency collections."""
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


def _elist(n, adj):
    """Edge list (u < v) from adjacency sets."""
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _cost(n, adj, D):
    """Number of vertex pairs at distance > D (0 means diameter <= D and connected)."""
    return lib.bad_pairs(n, _elist(n, adj), D)


def _pg_start(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Split-insert annealing: a bipartite graph is repaired by degree-preserving
# 2-switches, edge additions and removals, and "split-insert" growth moves.
# Growth frees one slot on each of k opposite-side vertices by deleting a
# random edge, then inserts a new vertex joined to them. Each state is scored
# by the number of pairs at distance > D; the best zero-cost state is kept.
# ----------------------------------------------------------------------------

def _anneal(n, edges, d, D, deadline, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, adj)
    log = []

    def add_e(u, v):
        adj[u].add(v)
        adj[v].add(u)
        log.append((True, u, v))

    def del_e(u, v):
        adj[u].discard(v)
        adj[v].discard(u)
        log.append((False, u, v))

    cost = _cost(n, adj, D)
    best_n, best_e, best_color = 0, None, None
    if cost == 0:
        best_n, best_e, best_color = n, _elist(n, adj), list(color)
    T = 0.6
    stale = 0

    while time.monotonic() < deadline:
        log.clear()
        grew = False
        r = rng.random()

        if cost == 0 and r < 0.15:
            # Split-insert growth.
            c = rng.randrange(2)
            cands = [s for s in range(n) if color[s] == 1 - c]
            k = min(len(cands), d - rng.randrange(0, 2))
            if k < 1:
                continue
            chosen = rng.sample(cands, k)
            for s in chosen:
                if len(adj[s]) >= d:
                    t = rng.choice(tuple(adj[s]))
                    del_e(s, t)
            v = n
            adj.append(set())
            color.append(c)
            n += 1
            grew = True
            for s in chosen:
                add_e(s, v)

        elif r < 0.6:
            # Degree-preserving 2-switch: (a,b),(c2,e) -> (a,e),(c2,b).
            a = rng.randrange(n)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            c2 = rng.randrange(n)
            if c2 == a or color[c2] != color[a] or not adj[c2]:
                continue
            e = rng.choice(tuple(adj[c2]))
            if e == b or e in adj[a] or b in adj[c2]:
                continue
            del_e(a, b)
            del_e(c2, e)
            add_e(a, e)
            add_e(c2, b)

        elif r < 0.8:
            # Add an edge between spare vertices on opposite sides.
            u = rng.randrange(n)
            if len(adj[u]) >= d:
                continue
            for _ in range(20):
                w = rng.randrange(n)
                if color[w] != color[u] and len(adj[w]) < d and w not in adj[u]:
                    add_e(u, w)
                    break

        else:
            # Remove a random edge.
            u = rng.randrange(n)
            if not adj[u]:
                continue
            w = rng.choice(tuple(adj[u]))
            del_e(u, w)

        if not log:
            continue

        new_cost = _cost(n, adj, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
            if cost == 0 and n > best_n:
                best_n, best_e, best_color = n, _elist(n, adj), list(color)
                stale = 0
            else:
                stale += 1
        else:
            for op, u, v in reversed(log):
                if op:
                    adj[u].discard(v)
                    adj[v].discard(u)
                else:
                    adj[u].add(v)
                    adj[v].add(u)
            if grew:
                adj.pop()
                color.pop()
                n -= 1
            stale += 1

        # Restart from the best valid state when the search stagnates.
        if stale > 3000 and best_e is not None:
            n = best_n
            adj = [set() for _ in range(n)]
            for u, v in best_e:
                adj[u].add(v)
                adj[v].add(u)
            color = list(best_color)
            cost = 0
            log.clear()
            stale = 0

    if best_e is None:
        return None
    return best_n, best_e


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Moore graph for D = 3 when d - 1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Starting graphs: all are valid and bipartite; pick the largest.
    starts = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    pg = _pg_start(d)
    if pg is not None:
        starts.append(pg)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            starts.append(lib.araujo_lopez_graph(d - 2))
        except (ValueError, StopIteration, KeyError):
            pass

    best = None
    for n0, e0 in starts:
        if lib.is_valid(n0, e0, d, D) and (best is None or n0 > best[0]):
            best = (n0, e0)
    if best is None:
        best = lib.haar_graph(d, range(d))

    # Spend the remaining budget on split-insert annealing from the best start.
    res = _anneal(best[0], best[1], d, D, deadline, rng)
    if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
        best = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
