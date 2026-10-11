import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane and generalized quadrangle W(q).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated-annealing growth: insert one vertex at a time into a bipartite
# graph with max degree d, then rewire by degree-preserving 2-switches and
# deficiency-filling edge additions until the bad-pair count reaches zero.
# ----------------------------------------------------------------------------

def _colour(n, adj):
    """Two-colouring of a bipartite graph given as adjacency sets; None if not bipartite."""
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
                elif col[v] == col[u]:
                    return None
    return col


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitset BFS)."""
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


def _insert(n, A, C, d, c, rng):
    """Append a new vertex of colour c, joined to up to d opposite-colour vertices.

    Deficient vertices are preferred; a saturated neighbour gives up one random edge.
    Maximum degree stays <= d. Returns the new vertex count.
    """
    v = n
    A.append(set())
    C.append(c)
    cands = [x for x in range(n) if C[x] != c]
    rng.shuffle(cands)
    cands.sort(key=lambda x: len(A[x]) >= d)
    for x in cands[:d]:
        if len(A[x]) >= d:
            w = rng.choice(tuple(A[x]))
            A[x].discard(w)
            A[w].discard(x)
        A[x].add(v)
        A[v].add(x)
    return n + 1


def _sa(n, A, C, d, D, cost, rng, deadline, steps, T):
    """Annealing on bad-pair cost. Moves keep bipartiteness and max degree <= d."""
    for it in range(steps):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        if rng.random() < 0.4:
            # Add an edge between two deficient opposite-colour vertices.
            d0 = [x for x in range(n) if C[x] == 0 and len(A[x]) < d]
            d1 = [y for y in range(n) if C[y] == 1 and len(A[y]) < d]
            if not d0 or not d1:
                continue
            x = rng.choice(d0)
            y = rng.choice(d1)
            if y in A[x]:
                continue
            A[x].add(y)
            A[y].add(x)
            new = _bad(n, A, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                A[x].discard(y)
                A[y].discard(x)
        else:
            # Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b).
            a = rng.randrange(n)
            if not A[a]:
                continue
            b = rng.choice(tuple(A[a]))
            c = rng.randrange(n)
            if c == a or C[c] != C[a] or not A[c]:
                continue
            e = rng.choice(tuple(A[c]))
            if e == b or e in A[a] or b in A[c]:
                continue
            A[a].discard(b)
            A[b].discard(a)
            A[c].discard(e)
            A[e].discard(c)
            A[a].add(e)
            A[e].add(a)
            A[c].add(b)
            A[b].add(c)
            new = _bad(n, A, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                A[a].discard(e)
                A[e].discard(a)
                A[c].discard(b)
                A[b].discard(c)
                A[a].add(b)
                A[b].add(a)
                A[c].add(e)
                A[e].add(c)
    return cost


def _grow_search(base, d, D, moore, deadline, rng):
    """Repeatedly insert a vertex and anneal until diameter <= D; return the largest graph found."""
    n0, e0 = base
    adj = [set() for _ in range(n0)]
    for u, v in e0:
        adj[u].add(v)
        adj[v].add(u)
    col = _colour(n0, adj)
    if col is None:
        return None
    best_n, best_adj, best_col = n0, adj, col
    fails = 0
    while best_n < moore and fails < 40 and time.monotonic() < deadline:
        A = [set(s) for s in best_adj]
        C = list(best_col)
        n_t = _insert(best_n, A, C, d, rng.randrange(2), rng)
        cost = _bad(n_t, A, D)
        cost = _sa(n_t, A, C, d, D, cost, rng, deadline, 2000, 0.6)
        if cost == 0:
            best_n, best_adj, best_col = n_t, A, C
            fails = 0
        else:
            fails += 1
    if best_n == n0:
        return None
    edges = [(u, v) for u in range(best_n) for v in best_adj[u] if u < v]
    return best_n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    base = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    try:
        cands = []
        if D >= 3:
            cands.append(_pg_base(d))
        if D >= 4:
            cands.append(_best_gq(d))
        for cand in cands:
            if cand is not None and cand[0] > base[0] and lib.is_valid(cand[0], cand[1], d, D):
                base = cand

        if d >= 2 and D >= 3 and base[0] < moore:
            grown = _grow_search(base, d, D, moore, deadline, rng)
            if grown is not None and grown[0] > base[0] and lib.is_valid(grown[0], grown[1], d, D):
                base = grown
    except Exception:
        pass

    try:
        valid = lib.is_valid(base[0], base[1], d, D)
    except Exception:
        valid = False
    if not valid:
        base = lib.haar_graph(d, range(d))
    return base
