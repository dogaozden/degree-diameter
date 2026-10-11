import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base graphs from the parent: projective planes (D = 3) and W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d, count=1):
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            if len(out) == count:
                break
    return out


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
# Graph helpers.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
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
# NEW construction: bi-Cayley (Haar-type) graphs over finite groups.
#
# Group G of order g with elements 0..g-1. Vertices a_x and b_y (x, y in G).
# Connection set S (|S| = d) gives edges a_x -- b_{x*s} for s in S. Left
# multiplication by any h is an automorphism, so the diameter test reduces to
# two BFS runs, from a_e and from b_e. The groups are Z_m x|_r Z_k, which covers
# cyclic groups (k = 1) and many non-abelian ones.
# Search: hill-climb / anneal S to minimise the number of vertex pairs left
# outside radius D, for increasing orders g.
# ----------------------------------------------------------------------------

def _divisors(G):
    return [k for k in range(1, G + 1) if G % k == 0]


def _group_params(G, rng):
    params = []
    for k in _divisors(G):
        m = G // k
        if m == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if not rs:
            continue
        sample = rng.sample(rs, min(3, len(rs)))
        if 1 in rs and 1 not in sample:
            sample[0] = 1
        for r in sample:
            params.append((m, k, r))
    rng.shuffle(params)
    return params


def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    G = m * k
    powers = np.array([pow(r, b, m) if m > 1 else 0 for b in range(k)], dtype=np.int64)
    X = np.arange(G, dtype=np.int64)
    A = X // k
    B = X % k
    a = (A[:, None] + powers[B][:, None] * A[None, :]) % m
    b = (B[:, None] + B[None, :]) % k
    return a * k + b


def _inverses(M):
    G = M.shape[0]
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return inv


def _cost(S, M, inv, G, d, D):
    """Number of vertex pairs at distance > D, computed from the two base sources a_e and b_e."""
    Sa = np.array(S, dtype=np.int64)
    Si = inv[Sa]
    N = np.empty((2 * G, d), dtype=np.int64)
    N[:G] = G + M[:, Sa]
    N[G:] = M[:, Si]
    total = 0
    for src in (0, G):
        vis = np.zeros(2 * G, dtype=bool)
        vis[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = N[fr].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            fr = nb
        total += 2 * G - int(vis.sum())
    return total


def _hill(M, inv, G, d, D, rng, steps, deadline):
    S = rng.sample(range(G), d)
    cost = _cost(S, M, inv, G, d, D)
    T = 0.6
    for it in range(steps):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(S2, M, inv, G, d, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
        T = max(0.05, T * 0.998)
    return S if cost == 0 else None


# ----------------------------------------------------------------------------
# Vertex insertion by annealing (kept from the parent as a final polish).
# ----------------------------------------------------------------------------

def _sets_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_sets(N, adj, D):
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _apply(adj, op):
    kind, a, b = op
    if kind == 'add':
        adj[a].add(b)
        adj[b].add(a)
    else:
        adj[a].discard(b)
        adj[b].discard(a)


def _undo(adj, op):
    kind, a, b = op
    if kind == 'add':
        adj[a].discard(b)
        adj[b].discard(a)
    else:
        adj[a].add(b)
        adj[b].add(a)


def _anneal_add(n, edges, d, D, deadline, rng, T0=0.8):
    if n < 2 or not edges:
        return None
    adj = _sets_from_edges(n, edges)
    color = _bipartition(n, [list(s) for s in adj])
    c = rng.randrange(2)
    opp = [x for x in range(n) if color[x] == 1 - c]
    if not opp:
        return None
    v = n
    N = n + 1
    adj.append(set())
    cur = _bad_sets(N, adj, D)
    it = 0
    while time.monotonic() < deadline:
        if cur == 0:
            new_edges = [(a, b) for a in range(N) for b in adj[a] if a < b]
            if lib.is_valid(N, new_edges, d, D):
                return N, new_edges
            return None
        it += 1
        t = opp[rng.randrange(len(opp))]
        if t in adj[v]:
            continue
        ops = []
        if len(adj[v]) >= d:
            s = rng.choice(tuple(adj[v]))
            ops.append(('del', v, s))
        if len(adj[t]) >= d:
            u = rng.choice(tuple(adj[t]))
            ops.append(('del', t, u))
        ops.append(('add', v, t))
        for op in ops:
            _apply(adj, op)
        new = _bad_sets(N, adj, D)
        delta = new - cur
        T = max(0.05, T0 * (0.999 ** it))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            for op in reversed(ops):
                _undo(adj, op)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * float(time_limit)
    s1_deadline = start + 0.6 * total
    s2_deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bound = lib._moore_bound(d, D)
    if best[0] >= bound:
        return best

    # Stage 0: algebraic bases from the parent.
    if D == 3:
        for b in _best_pg(d, 2):
            consider(b[0], b[1])
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= s1_deadline:
                break
            b = _gq_w(q)
            consider(b[0], b[1])
    if best[0] >= bound:
        return best

    # Stage 1: bi-Cayley search over groups, from the current best order upward.
    Gmax = bound // 2
    G = max(best[0] // 2 + 1, d)
    while G <= Gmax and time.monotonic() < s1_deadline:
        success = False
        for (m, k, r) in _group_params(G, rng):
            if time.monotonic() >= s1_deadline:
                break
            M = _table(m, k, r)
            inv = _inverses(M)
            S = _hill(M, inv, G, d, D, rng, 1500, s1_deadline)
            if S is not None:
                mulf = (lambda x, g, M=M: int(M[x, g]))
                edges = lib.group_lift(2, [(0, 1, s) for s in S], G, mulf)[1]
                consider(2 * G, edges)
                success = True
                break
        if not success:
            break
        G += 1

    # Stage 2: annealed vertex insertion on the best graph.
    while best[0] >= 2 and time.monotonic() < s2_deadline:
        slice_end = min(s2_deadline, time.monotonic() + 4.0)
        res = _anneal_add(best[0], best[1], d, D, slice_end, rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    return best
