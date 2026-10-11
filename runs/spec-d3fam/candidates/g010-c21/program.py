import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartition helper.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists (0/1 per vertex)."""
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


# ----------------------------------------------------------------------------
# Base graphs: every base has max degree <= d and diameter <= D.
# ----------------------------------------------------------------------------

def _bases(d, D):
    """K_{d,d} always; for D >= 3 also the Araujo-Pardo-Lopez graph and the largest PG(2,q) incidence graph."""
    out = [lib.haar_graph(d, range(d))]
    if D >= 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
    return out


# ----------------------------------------------------------------------------
# NEW HELPER: matching-swap vertex pair insertion.
#
# Pick a matching M = {(a_i, b_i)} of d edges (a_i on side A, b_i on side B)
# and delete it. Add a new A-vertex x joined to all b_i and a new B-vertex y
# joined to all a_i. Every old vertex keeps its degree, x and y reach degree d,
# and the graph stays bipartite. Two vertices are gained per success. The
# matching is found by simulated annealing that minimises the number of vertex
# pairs at distance > D.
# ----------------------------------------------------------------------------

def _compatible(M, e, skip):
    """True if edge e = (a, b) keeps M (minus index skip) a matching."""
    a, b = e
    for i, (a2, b2) in enumerate(M):
        if i != skip and (a2 == a or b2 == b):
            return False
    return True


def _swap_once(n, edges, d, D, deadline, rng, iters):
    """Try to insert one pair (x on side A, y on side B) by annealing a matching; return (n+2, edges) or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    E = list({((u, v) if color[u] == 0 else (v, u)) for u, v in edges})
    if len(E) < d:
        return None

    def build_edges(M):
        Ms = set(M)
        x, y = n, n + 1
        out = [e for e in E if e not in Ms]
        out += [(x, b) for _, b in M]
        out += [(y, a) for a, _ in M]
        return out

    def cost(M):
        out = build_edges(M)
        return lib.bad_pairs(n + 2, out, D)

    # Greedy random initial matching of size d.
    rng.shuffle(E)
    M = []
    for e in E:
        if len(M) == d:
            break
        if _compatible(M, e, -1):
            M.append(e)
    if len(M) < d:
        return None

    c = cost(M)
    T0 = 4.0
    for it in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - it / iters) + 0.05
        i = rng.randrange(d)
        e = E[rng.randrange(len(E))]
        if e in M or not _compatible(M, e, i):
            continue
        T_M = M[:]
        T_M[i] = e
        c2 = cost(T_M)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            M, c = T_M, c2

    if c != 0:
        return None
    return n + 2, build_edges(M)


def _grow_swaps(n, edges, d, D, deadline, rng):
    """Repeatedly insert vertex pairs by matching-swap until the deadline; return the largest valid (n, edges)."""
    best = (n, edges)
    while time.monotonic() < deadline:
        res = _swap_once(n, edges, d, D, deadline, rng, 3000)
        if res is None:
            if time.monotonic() >= deadline:
                break
            continue
        n, edges = res
        best = res
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Moore-optimal case: PG(2, d-1) incidence graph is d-regular with diameter 3.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    bases = [g for g in _bases(d, D) if lib.is_valid(g[0], g[1], d, D)]
    bases.sort(key=lambda g: -g[0])
    best = bases[0]

    # Spend the search budget on the largest bases, sharing time among them.
    for idx, g in enumerate(bases):
        now = time.monotonic()
        share = (deadline - now) / (len(bases) - idx)
        if share <= 0:
            break
        try:
            res = _grow_swaps(g[0], g[1], d, D, now + share, rng)
            if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
