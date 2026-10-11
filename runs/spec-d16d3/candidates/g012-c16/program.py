import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Growth-and-repair family (D >= 3).
#
# Start from the incidence graph of PG(2, q), q the largest prime power with
# q + 1 <= d. Its diameter is 3, so it is valid for every D >= 3. Then grow it
# one vertex pair at a time: a new point-side vertex and a new line-side vertex
# are attached to spare capacity of the existing graph, and the graph is
# repaired by degree-preserving double edge swaps (plus edge additions) under
# simulated annealing, minimising the number of vertex pairs farther than D apart.
# A grown graph is stored only if lib.is_valid confirms it, so the fallbacks
# always stand.
# ----------------------------------------------------------------------------


def _best_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


class _State:
    """Bipartite graph with colour 0 (A side) and 1 (B side); E holds (a, b) pairs with a in A."""

    def __init__(self, n, color, adj, E, d):
        self.n = n
        self.color = color
        self.adj = adj
        self.E = E
        self.d = d

    def clone(self):
        return _State(self.n, list(self.color), [set(s) for s in self.adj],
                      list(self.E), self.d)

    def edges(self):
        return [(a, b) for a, b in self.E]


def _bad_pairs(n, adj, D):
    """Ordered count of vertex pairs at distance > D (each unordered pair counted twice)."""
    nb = [list(s) for s in adj]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _grow(st, rng):
    """Add one A-side and one B-side vertex, joined to each other and to spare old capacity."""
    n = st.n
    a, b = n, n + 1
    st.color.extend([0, 1])
    st.adj.extend([set(), set()])
    st.n = n + 2
    st.adj[a].add(b)
    st.adj[b].add(a)
    st.E.append((a, b))
    bspare = [v for v in range(n) if st.color[v] == 1 and len(st.adj[v]) < st.d]
    aspare = [v for v in range(n) if st.color[v] == 0 and len(st.adj[v]) < st.d]
    rng.shuffle(bspare)
    rng.shuffle(aspare)
    for v in bspare[: st.d - 1]:
        st.adj[a].add(v)
        st.adj[v].add(a)
        st.E.append((a, v))
    for v in aspare[: st.d - 1]:
        st.adj[b].add(v)
        st.adj[v].add(b)
        st.E.append((v, b))


def _anneal(st, D, rng, deadline, iters):
    """Repair by annealing; returns True iff the final state has no pair farther than D."""
    n, adj, E, d, color = st.n, st.adj, st.E, st.d, st.color
    cost = _bad_pairs(n, adj, D)
    if cost == 0:
        return True
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    T0, T1 = 1.5, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if rng.random() < 0.85 and len(E) >= 2:
            # Degree-preserving double edge swap.
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            adj[a1].discard(b1)
            adj[b1].discard(a1)
            adj[a2].discard(b2)
            adj[b2].discard(a2)
            adj[a1].add(b2)
            adj[b2].add(a1)
            adj[a2].add(b1)
            adj[b1].add(a2)
            new = _bad_pairs(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
                E[i] = (a1, b2)
                E[j] = (a2, b1)
            else:
                adj[a1].discard(b2)
                adj[b2].discard(a1)
                adj[a2].discard(b1)
                adj[b1].discard(a2)
                adj[a1].add(b1)
                adj[b1].add(a1)
                adj[a2].add(b2)
                adj[b2].add(a2)
        else:
            # Edge addition between two vertices with spare capacity.
            a = rng.choice(A)
            b = rng.choice(B)
            if b in adj[a] or len(adj[a]) >= d or len(adj[b]) >= d:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _bad_pairs(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
                E.append((a, b))
            else:
                adj[a].discard(b)
                adj[b].discard(a)
    return cost == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Cycle of length 2D: bipartite, degree 2, diameter D (Moore-optimal).
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def store(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    q = _best_q(d)
    if q is None:
        return best

    # PG(2, q) incidence: diameter 3, degree q + 1 <= d.
    m2, base_e = lib.projective_plane_incidence(q)
    m = m2 // 2
    store(m2, base_e)

    color = [0] * m + [1] * m
    adj = [set() for _ in range(m2)]
    E = []
    for u, v in base_e:
        adj[u].add(v)
        adj[v].add(u)
        E.append((u, v))
    cur = _State(m2, color, adj, E, d)

    fails = 0
    while fails < 3 and time.monotonic() < deadline - 0.5:
        trial = cur.clone()
        _grow(trial, rng)
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, 0.3 * remaining))
        if _anneal(trial, D, rng, slice_end, iters=4000):
            cur = trial
            fails = 0
            store(cur.n, cur.edges())
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
