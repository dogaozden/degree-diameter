import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New idea: degree-preserving vertex-PAIR insertion by edge re-threading.
#
# Given a bipartite graph with max degree d, pick d-1 pairwise disjoint edges
# (y_i, x_i) with y_i on side A and x_i on side B. Remove them and add a new
# A-vertex a joined to every x_i, a new B-vertex b joined to every y_i, and the
# edge a-b. Each x_i and y_i keeps its degree, a and b get degree exactly d, and
# the order grows by 2 while the edge count grows by d. The result is bipartite
# by construction, so only the diameter must be checked. The choice of the d-1
# edges is searched by simulated annealing on lib.bad_pairs.
# ----------------------------------------------------------------------------

def _colors(n, edges):
    """Two-colouring by BFS. Returns list of colours in {0, 1}."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _pair_grow_once(n, E, d, D, deadline, rng):
    """Try to insert one vertex pair (a, b) with diameter <= D. Returns (n+2, edges) or None."""
    need = d - 1
    if need < 1 or n + 2 > lib._moore_bound(d, D):
        return None
    m = len(E)
    if m < need:
        return None
    color = _colors(n, E)
    # oriented[i] = (A-endpoint y, B-endpoint x) for edge E[i].
    oriented = [(u, v) if color[u] == 0 else (v, u) for u, v in E]
    a, b = n, n + 1

    def edges_for(sel):
        ss = set(sel)
        out = [E[i] for i in range(m) if i not in ss]
        for i in sel:
            y, x = oriented[i]
            out.append((a, x))
            out.append((b, y))
        out.append((a, b))
        return out

    # Random initial matching of size d-1 (distinct A-ends and distinct B-ends).
    order = list(range(m))
    rng.shuffle(order)
    sel, usedA, usedB = [], set(), set()
    for i in order:
        y, x = oriented[i]
        if y in usedA or x in usedB:
            continue
        sel.append(i)
        usedA.add(y)
        usedB.add(x)
        if len(sel) == need:
            break
    if len(sel) < need:
        return None

    cost = lib.bad_pairs(n + 2, edges_for(sel), D)
    best_cost = cost
    T, stale = 1.0, 0
    while cost > 0:
        if time.monotonic() > deadline or stale > 600:
            break
        j = rng.randrange(need)
        old = sel[j]
        y0, x0 = oriented[old]
        usedA.discard(y0)
        usedB.discard(x0)
        new = -1
        for _ in range(30):
            c = rng.randrange(m)
            if c in sel:
                continue
            y, x = oriented[c]
            if y in usedA or x in usedB:
                continue
            new = c
            break
        if new < 0:
            usedA.add(y0)
            usedB.add(x0)
            stale += 1
            continue
        sel2 = sel[:]
        sel2[j] = new
        c2 = lib.bad_pairs(n + 2, edges_for(sel2), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            sel = sel2
            cost = c2
            y, x = oriented[new]
            usedA.add(y)
            usedB.add(x)
            if cost < best_cost:
                best_cost = cost
                stale = 0
            else:
                stale += 1
        else:
            usedA.add(y0)
            usedB.add(x0)
            stale += 1
        T = max(0.2, T * 0.998)

    if cost == 0:
        return n + 2, edges_for(sel)
    return None


def _pair_chain(n, E, d, D, deadline, rng):
    """Repeatedly insert vertex pairs until the deadline or no further insertion is possible."""
    if d - 1 < 1:
        return n, E
    while time.monotonic() < deadline:
        if n + 2 > lib._moore_bound(d, D):
            break
        r = _pair_grow_once(n, E, d, D, deadline, rng)
        if r is None:
            continue
        n, E = r
    return n, E


# ----------------------------------------------------------------------------
# Main entry point.
#
# Scope: this island scores D = 3 targets. For D >= 4 the program returns the
# simple K_{d,d} fallback (valid for D >= 2); the other families from the
# parent are not included here.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D == 3:
        # Araujo-Pardo & López record base when d - 2 is a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, E = lib.araujo_lopez_graph(d - 2)
                consider(n, E)
            except ValueError:
                pass
        # Plain projective plane incidence graph.
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # New: grow the best base by degree-preserving vertex-pair insertion.
        base_n, base_E = best_n, best_E
        n2, E2 = _pair_chain(base_n, base_E, d, D, deadline, rng)
        if n2 > base_n:
            consider(n2, E2)

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, [tuple(e) for e in best_E]
