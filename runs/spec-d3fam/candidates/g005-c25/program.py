import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for D = 3: start from the best known algebraic graph and grow it
# by vertex-pair insertion, then repair with degree-preserving 2-switches and
# threshold annealing on the number of pairs at distance > 3.
# Every candidate is re-verified with lib.is_valid before it can be returned.
# ----------------------------------------------------------------------------


def _moore3(d):
    """Largest order of a bipartite graph with max degree d and diameter 3."""
    return 2 * (1 + (d - 1) + (d - 1) ** 2)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _colors(n, edges):
    """Two-colouring of a bipartite graph given as an edge list."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (adj is a list of neighbour sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _State:
    """Bipartite graph with side labels, edge list with O(1) removal, degree cap d."""

    def __init__(self, n, color, edges, d):
        self.n = n
        self.d = d
        self.color = color
        self.adj = [set() for _ in range(n)]
        self.elist = []
        self.pos = {}
        for u, v in edges:
            if color[u] == 0:
                self.add_edge(u, v)
            else:
                self.add_edge(v, u)

    def add_edge(self, a, b):
        # a is on side 0, b on side 1
        self.adj[a].add(b)
        self.adj[b].add(a)
        self.pos[(a, b)] = len(self.elist)
        self.elist.append((a, b))

    def remove_edge(self, a, b):
        self.adj[a].discard(b)
        self.adj[b].discard(a)
        i = self.pos.pop((a, b))
        last = self.elist.pop()
        if last != (a, b):
            self.elist[i] = last
            self.pos[last] = i


def _fill(st, rng):
    """Greedily join deficient opposite-side vertices. Returns number of edges added."""
    d = st.d
    A = [v for v in range(st.n) if st.color[v] == 0 and len(st.adj[v]) < d]
    B = [v for v in range(st.n) if st.color[v] == 1 and len(st.adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    added = 0
    for a in A:
        for b in B:
            if len(st.adj[a]) >= d:
                break
            if len(st.adj[b]) < d and b not in st.adj[a]:
                st.add_edge(a, b)
                added += 1
    return added


def _propose(st, rng):
    """Random degree-respecting move as a list of (is_add, a, b) operations, or None."""
    d = st.d
    E = st.elist
    if len(E) < 2:
        return None
    if rng.random() < 0.6:
        # double-edge swap: keeps every degree fixed
        a1, b1 = E[rng.randrange(len(E))]
        a2, b2 = E[rng.randrange(len(E))]
        if a1 == a2 or b1 == b2 or b2 in st.adj[a1] or b1 in st.adj[a2]:
            return None
        return [(False, a1, b1), (False, a2, b2), (True, a1, b2), (True, a2, b1)]
    a, b = E[rng.randrange(len(E))]
    if rng.random() < 0.5:
        # move the A-end of edge (a, b) to a deficient A-vertex x
        X = [x for x in range(st.n)
             if st.color[x] == 0 and x != a and len(st.adj[x]) < d and b not in st.adj[x]]
        if not X:
            return None
        x = X[rng.randrange(len(X))]
        return [(False, a, b), (True, x, b)]
    # move the B-end of edge (a, b) to a deficient B-vertex y
    Y = [y for y in range(st.n)
         if st.color[y] == 1 and y != b and len(st.adj[y]) < d and a not in st.adj[y]]
    if not Y:
        return None
    y = Y[rng.randrange(len(Y))]
    return [(False, a, b), (True, a, y)]


def _apply(st, ops):
    for is_add, a, b in ops:
        if is_add:
            st.add_edge(a, b)
        else:
            st.remove_edge(a, b)


def _undo(st, ops):
    for is_add, a, b in reversed(ops):
        if is_add:
            st.remove_edge(a, b)
        else:
            st.add_edge(a, b)


def _anneal(st, D, deadline, rng, iters):
    """Threshold annealing on the count of pairs at distance > D. True iff it reaches 0."""
    _fill(st, rng)
    cur = _bad_pairs(st.n, st.adj, D)
    for it in range(iters):
        if cur == 0:
            return True
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        ops = _propose(st, rng)
        if ops is None:
            continue
        _apply(st, ops)
        new = _bad_pairs(st.n, st.adj, D)
        if new <= cur - T * math.log(1.0 - rng.random()):
            cur = new
            if _fill(st, rng):
                cur = _bad_pairs(st.n, st.adj, D)
        else:
            _undo(st, ops)
    return cur == 0


def _insert_pair(n, color, edges, d, rng):
    """Add new vertices x (side 0) and y (side 1). Remove a random matching of up to d
    edges (a_i, b_i) and join x to every b_i and y to every a_i. Degrees of old vertices
    are unchanged. Returns (n2, edges2, color2) or None."""
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    rng.shuffle(E)
    ua, ub, M = set(), set(), []
    for a, b in E:
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        M.append((a, b))
        if len(M) == d:
            break
    if not M:
        return None
    x, y = n, n + 1
    removed = set(M)
    new_edges = [(a, b) for a, b in E if (a, b) not in removed]
    for a, b in M:
        new_edges.append((x, b))
        new_edges.append((a, y))
    return n + 2, new_edges, list(color) + [0, 1]


def _grow(n, edges, d, D, cap, deadline, rng):
    """Repeatedly insert a vertex pair and anneal until diameter <= D again."""
    cur_n, cur_e = n, list(edges)
    cur_c = _colors(cur_n, cur_e)
    best = (cur_n, cur_e)
    while time.monotonic() < deadline and cur_n + 2 <= cap:
        ins = _insert_pair(cur_n, cur_c, cur_e, d, rng)
        if ins is None:
            break
        n2, e2, c2 = ins
        st = _State(n2, c2, e2, d)
        if _anneal(st, D, deadline, rng, 4000):
            e_new = list(st.elist)
            if lib.is_valid(n2, e_new, d, D):
                cur_n, cur_e, cur_c = n2, e_new, c2
                best = (cur_n, cur_e)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        # Araujo-Pardo & Lopez record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 3:
        cap = _moore3(d)
        if best[0] + 2 <= cap:
            try:
                n2, e2 = _grow(best[0], best[1], d, D, cap, deadline, rng)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
