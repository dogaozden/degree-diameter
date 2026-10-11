import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _oriented(n, edges):
    """Return the edge list with every pair written as (side-0 vertex, side-1 vertex)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = _bipartition(n, adj)
    return [(u, v) if col[u] == 0 else (v, u) for u, v in edges]


def _base_candidates(d, D):
    """Known structured starting graphs (each checked for validity by the caller)."""
    out = []
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            out.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    return out


# ----------------------------------------------------------------------------
# Degree-preserving state with incremental adjacency.
#
# A state is an n-vertex bipartite graph stored as a list E of (side0, side1)
# pairs. Every move keeps all degrees fixed except the split move, which only
# creates vertices of degree exactly d.
# ----------------------------------------------------------------------------

class _State:
    def __init__(self, n, E):
        self.n = n
        self.E = list(E)
        self.Eset = set(self.E)
        self.adj = [set() for _ in range(n)]
        for a, b in self.E:
            self.adj[a].add(b)
            self.adj[b].add(a)

    def replace(self, i, new):
        """Replace the i-th pair by `new`, keeping adjacency and the pair set in sync."""
        a, b = self.E[i]
        self.adj[a].discard(b)
        self.adj[b].discard(a)
        self.Eset.discard((a, b))
        c, e = new
        self.adj[c].add(e)
        self.adj[e].add(c)
        self.Eset.add((c, e))
        self.E[i] = (c, e)


def _cost(n, adj, D):
    """Ordered pairs at distance > D. Zero iff every pair is within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


# ----------------------------------------------------------------------------
# New move: vertex-pair splitting.
#
# Pick a matching M = {(a_i, b_i)} of size d-1. Delete its edges, add a new
# side-0 vertex x joined to every b_i, a new side-1 vertex y joined to every
# a_i, and the edge x-y. Every old degree is unchanged and x, y have degree d.
# The new vertices give +2 order but may break the diameter, so the state is
# then repaired by degree-preserving rewiring.
# ----------------------------------------------------------------------------

def _split(st, d, rng):
    order = st.E[:]
    rng.shuffle(order)
    used_a, used_b, M = set(), set(), []
    for a, b in order:
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        M.append((a, b))
        if len(M) == d - 1:
            break
    if len(M) < d - 1:
        return None
    x, y = st.n, st.n + 1
    Mset = set(M)
    newE = [p for p in st.E if p not in Mset]
    newE += [(x, b) for _, b in M]
    newE += [(a, y) for a, _ in M]
    newE.append((x, y))
    return _State(st.n + 2, newE)


# ----------------------------------------------------------------------------
# Degree-preserving repair: 2-switch rewiring under Metropolis acceptance.
# (a,b),(c,e) -> (a,e),(c,b) keeps bipartiteness and every degree.
# ----------------------------------------------------------------------------

def _try_switch(st, rng):
    m = len(st.E)
    i, j = rng.randrange(m), rng.randrange(m)
    if i == j:
        return None
    a, b = st.E[i]
    c, e = st.E[j]
    if a == c or b == e:
        return None
    if (a, e) in st.Eset or (c, b) in st.Eset:
        return None
    return i, j


def _repair(st, D, rng, deadline, iters):
    cost = _cost(st.n, st.adj, D)
    if cost == 0:
        return True
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        T = 2.0 * (0.025 ** (it / iters))
        mv = _try_switch(st, rng)
        if mv is None:
            continue
        i, j = mv
        a, b = st.E[i]
        c, e = st.E[j]
        st.replace(i, (a, e))
        st.replace(j, (c, b))
        c2 = _cost(st.n, st.adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost == 0:
                return True
        else:
            st.replace(i, (a, b))
            st.replace(j, (c, e))
    return cost == 0


# ----------------------------------------------------------------------------
# Driver: grow by splitting, repair, and keep the last valid state.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best_n, best_e = fb_n, fb_e

    for n0, e0 in _base_candidates(d, D):
        if n0 > best_n and lib.is_valid(n0, e0, d, D):
            best_n, best_e = n0, e0

    if best_n == fb_n and best_e is fb_e:
        pass  # keep fallback unless a base wins below

    cur = _State(best_n, _oriented(best_n, best_e))
    best = (best_n, list(cur.E))

    while time.monotonic() < deadline:
        nxt = _split(cur, d, rng)
        if nxt is None:
            break
        if _repair(nxt, D, rng, deadline, iters=800):
            cur = nxt
            best = (cur.n, list(cur.E))

    out_n, out_E = best
    out_edges = [(int(u), int(v)) for u, v in out_E]
    if lib.is_valid(out_n, out_edges, d, D):
        return out_n, out_edges
    return fb_n, fb_e
