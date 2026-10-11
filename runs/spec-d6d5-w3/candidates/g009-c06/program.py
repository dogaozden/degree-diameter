import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic seeds: projective plane, Araujo-Pardo-Lopez (D = 3), generalized
# quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Bipartite "side-parity" representation used by the search.
#   A-side vertices get even ids 0, 2, ..., 2h-2
#   B-side vertices get odd ids 1, 3, ..., 2h-1
# Growing by one pair appends ids 2h (A) and 2h+1 (B).
# ----------------------------------------------------------------------------

def _to_scheme(n, edges, d):
    """Return (h, adj) in the parity scheme if the graph is d-regular bipartite with equal sides, else None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return None
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
                elif color[v] == color[u]:
                    return None
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if len(A) != len(B) or not A:
        return None
    new = [0] * n
    for i, v in enumerate(A):
        new[v] = 2 * i
    for j, v in enumerate(B):
        new[v] = 2 * j + 1
    sadj = [[] for _ in range(n)]
    for v in range(n):
        sadj[new[v]] = [new[u] for u in adj[v]]
    return len(A), sadj


def _complete_scheme(d):
    """K_{d,d} in the parity scheme: valid for any D >= 2."""
    adj = [[] for _ in range(2 * d)]
    for i in range(d):
        adj[2 * i] = [2 * j + 1 for j in range(d)]
    for j in range(d):
        adj[2 * j + 1] = [2 * i for i in range(d)]
    return d, adj


def _swap(adj, a1, b1, a2, b2):
    """Replace edges a1-b1, a2-b2 by a1-b2, a2-b1 (in place)."""
    adj[a1][adj[a1].index(b1)] = b2
    adj[b1][adj[b1].index(a1)] = a2
    adj[a2][adj[a2].index(b2)] = b1
    adj[b2][adj[b2].index(a2)] = a1


def _cost(adj, N, D):
    """Ordered pairs at distance > D (zero means diameter <= D)."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nb = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb[v] = x
        ball = nb
    return N * N - sum(b.bit_count() for b in ball)


def _anneal(adj, h, d, D, rng, deadline, T0, T1):
    """Simulated annealing over degree-preserving 2-switches. Returns final cost (0 = success)."""
    N = 2 * h
    cur = _cost(adj, N, D)
    if cur == 0:
        return 0
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T1 / T0) ** frac
        a1 = 2 * rng.randrange(h)
        a2 = 2 * rng.randrange(h)
        if a1 == a2:
            continue
        b1 = adj[a1][rng.randrange(d)]
        b2 = adj[a2][rng.randrange(d)]
        if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        _swap(adj, a1, b1, a2, b2)
        c2 = _cost(adj, N, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            _swap(adj, a1, b2, a2, b1)  # revert
    return cur


def _grow(adj, h, d, rng):
    """Add one A-vertex (id 2h) and one B-vertex (id 2h+1) keeping d-regularity.

    Remove a matching of d-1 edges a_i-b_i; reattach a_i to the new B vertex and b_i to
    the new A vertex, then join the two new vertices. Returns False on failure.
    """
    A = list(range(0, 2 * h, 2))
    pairs = []
    for _ in range(50):
        rng.shuffle(A)
        usedB = set()
        pairs = []
        for a in A:
            if len(pairs) == d - 1:
                break
            cands = [b for b in adj[a] if b not in usedB]
            if not cands:
                continue
            b = rng.choice(cands)
            usedB.add(b)
            pairs.append((a, b))
        if len(pairs) == d - 1:
            break
    else:
        return False
    N = 2 * h
    a_new, b_new = N, N + 1
    adj.append([])
    adj.append([])
    for a, b in pairs:
        adj[a][adj[a].index(b)] = b_new
        adj[b][adj[b].index(a)] = a_new
        adj[a_new].append(b)
        adj[b_new].append(a)
    adj[a_new].append(b_new)
    adj[b_new].append(a_new)
    return True


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        m = 2 * D  # even cycle C_{2D}: diameter D, bipartite
        return m, [(i, (i + 1) % m) for i in range(m)]

    # Safe fallback: K_{d,d} (diameter 2).
    best_n = 2 * d
    best_edges = [(i, d + j) for i in range(d) for j in range(d)]
    target = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_edges
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e

    algebraic = []
    if D >= 3:
        try:
            if lib.is_prime_power(d - 1):
                algebraic.append(lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        try:
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                algebraic.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
        try:
            algebraic.append(_gq_w(d - 1))
        except Exception:
            pass

    seed_h, seed_adj = _complete_scheme(d)
    for n, e in algebraic:
        consider(n, e)
        if lib.is_valid(n, e, d, D):
            sch = _to_scheme(n, e, d)
            if sch is not None and sch[0] > seed_h:
                seed_h, seed_adj = sch

    if best_n >= target:
        return best_n, best_edges

    # Bold search: grow a regular bipartite graph one vertex-pair at a time, repairing
    # each step by annealed 2-switches that drive the number of far pairs to zero.
    valid_h, valid_adj = seed_h, [list(x) for x in seed_adj]
    anneal_best = (valid_h, valid_adj)
    fails = 0
    while time.monotonic() < deadline - 0.5 and fails < 10000:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = now + min(remaining, max(2.0, 0.25 * remaining))
        cand = [list(x) for x in valid_adj]
        if not _grow(cand, valid_h, d, rng):
            fails += 1
            continue
        h2 = valid_h + 1
        c = _anneal(cand, h2, d, D, rng, slice_end, 3.0, 0.2)
        if c == 0:
            valid_h, valid_adj = h2, cand
            anneal_best = (h2, cand)
            if 2 * h2 >= target:
                break
        else:
            fails += 1

    h, adj = anneal_best
    if h * 2 > best_n:
        n = 2 * h
        e = [(a, b) for a in range(0, n, 2) for b in adj[a]]
        consider(n, e)

    if not lib.is_valid(best_n, best_edges, d, D):
        best_n = 2 * d
        best_edges = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, best_edges
