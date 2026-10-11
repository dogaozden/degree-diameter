import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy: surgery on a valid record-quality base graph.
#
# Take a valid bipartite graph G of max degree d and diameter <= D. Pick a
# matching R of k edges (k = d, or d-1 with an extra A-B edge) and delete it.
# Add two new vertices a (A side) and b (B side). Join a to the freed B-ends
# and b to the freed A-ends, plus a-b when k = d-1. Degrees are preserved and
# the order grows by 2. Simulated annealing swaps edges in R to drive the
# number of pairs at distance > D to zero. Each success becomes the new base,
# so the search repeats until the time budget is spent.
#
# Every candidate is checked with lib.is_valid before it is accepted. If no
# surgery succeeds, the largest valid base is returned.
# ----------------------------------------------------------------------------


def _two_color(n, edges):
    """Proper 2-colouring of a bipartite graph (vertices with no edges get colour 0)."""
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


def _base_candidates(d, D):
    """Return the largest valid (n, edges) among the known constructions, or None."""
    cands = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    if D >= 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))
    best = None
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    return best


def _surgery_edges(base_n, E, R, mode_ab):
    """Edges of the graph after removing matching R and attaching new vertices a (= base_n), b (= base_n + 1)."""
    a, b = base_n, base_n + 1
    Rs = set(R)
    edges = [e for e in E if e not in Rs]
    for x, y in R:
        edges.append((y, a))
        edges.append((x, b))
    if mode_ab:
        edges.append((a, b))
    return edges


def _cost(base_n, E, R, mode_ab, D):
    """Number of vertex pairs at distance > D in the surgered graph. Zero means valid."""
    edges = _surgery_edges(base_n, E, R, mode_ab)
    return lib.bad_pairs(base_n + 2, edges, D)


def _try_surgery(base_n, E, d, D, rng, deadline, iters):
    """Anneal a removed matching R so the surgered graph has diameter <= D. Return (mode_ab, R) or None."""
    mode_ab = rng.random() < 0.5
    k = d - 1 if mode_ab else d
    if k < 1 or len(E) < k:
        return None

    # Random initial matching of k edges with distinct endpoints.
    order = E[:]
    rng.shuffle(order)
    R = []
    used_x, used_y = set(), set()
    for x, y in order:
        if len(R) == k:
            break
        if x in used_x or y in used_y:
            continue
        R.append((x, y))
        used_x.add(x)
        used_y.add(y)
    if len(R) < k:
        return None

    cur = _cost(base_n, E, R, mode_ab, D)
    if cur == 0:
        return mode_ab, R

    for it in range(iters):
        if time.monotonic() > deadline:
            break
        T = 1.0 * (0.02 ** (it / iters))
        i = rng.randrange(k)
        ox = {R[j][0] for j in range(k) if j != i}
        oy = {R[j][1] for j in range(k) if j != i}
        Rset = set(R)
        cand = None
        for _ in range(60):
            e = E[rng.randrange(len(E))]
            if e[0] in ox or e[1] in oy or e in Rset:
                continue
            cand = e
            break
        if cand is None:
            continue
        newR = R[:]
        newR[i] = cand
        c2 = _cost(base_n, E, newR, mode_ab, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            R, cur = newR, c2
            if cur == 0:
                return mode_ab, R
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    base = _base_candidates(d, D)
    if base is None:
        return 2, [(0, 1)]

    best_n, best_E = base
    rng = random.Random(seed)

    try:
        color = _two_color(best_n, best_E)
        while time.monotonic() < deadline:
            E = [(u, v) if color[u] == 0 else (v, u) for u, v in best_E]
            res = _try_surgery(best_n, E, d, D, rng, deadline, iters=600)
            if res is None:
                continue
            mode_ab, R = res
            new_E = _surgery_edges(best_n, E, R, mode_ab)
            new_n = best_n + 2
            if lib.is_valid(new_n, new_E, d, D):
                best_n, best_E = new_n, new_E
                color = color + [0, 1]
    except Exception:
        pass

    if not lib.is_valid(best_n, best_E, d, D):
        fb = _base_candidates(d, D)
        if fb is None:
            return 2, [(0, 1)]
        return fb
    return best_n, [tuple(e) for e in best_E]
