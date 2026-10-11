import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: PG(2, q) incidence (D = 3) and the generalized quadrangle W(q) (D >= 4).
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
# Adjacency-set helpers.
# ----------------------------------------------------------------------------

def _sets_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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


def _bad_sets(N, adj, D):
    """Number of unordered pairs at distance > D."""
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


def _saturate(n, edges, d, rng):
    """Add random opposite-side edges with spare degree. Never increases distances."""
    edges = list(edges)
    adj = _sets_from_edges(n, edges)
    deg = [len(s) for s in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            edges.append((a, b))
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Simulated-annealing insertion of one new vertex (steal-attach moves).
# ----------------------------------------------------------------------------

def _anneal_add(n, edges, d, D, deadline, rng, T0=0.8):
    """Try to insert one vertex by annealing its neighbourhood. Returns (n+1, edges) or None."""
    if n < 2 or not edges:
        return None
    adj = _sets_from_edges(n, edges)
    color = _bipartition(n, adj)
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
# Bold change: random walk over VALID graphs using degree-preserving 2-switches.
# The walk diversifies the spare-slot layout so that insertion can succeed later.
# ----------------------------------------------------------------------------

def _walk(N, adj, color, D, rng, deadline, steps):
    L = [v for v in range(N) if color[v] == 0 and adj[v]]
    if len(L) < 2:
        return
    for _ in range(steps):
        if time.monotonic() > deadline:
            break
        a = rng.choice(L)
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(L)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        ops = [('del', a, b), ('del', c, e), ('add', a, e), ('add', c, b)]
        for op in ops:
            _apply(adj, op)
        if _bad_sets(N, adj, D) == 0:
            continue  # accepted: still a valid graph
        for op in reversed(ops):
            _undo(adj, op)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Base graph.
    base = None
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                base = lib.projective_plane_incidence(q)
                break
    else:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                base = _gq_w(q)
                break
    if base is not None:
        consider(base[0], base[1])

    if base is None or best[0] >= lib._moore_bound(d, D):
        return best

    cur_n, cur_e = best
    cur_e = _saturate(cur_n, cur_e, d, rng)
    consider(cur_n, cur_e)
    cur_n, cur_e = best

    # Alternate: try to insert a vertex; if that fails, random-walk over valid graphs
    # to rearrange the spare slots, then try again.
    while time.monotonic() < deadline:
        now = time.monotonic()
        res = _anneal_add(cur_n, cur_e, d, D, min(deadline, now + 3.0), rng)
        if res is not None:
            n2, e2 = res
            e2 = _saturate(n2, e2, d, rng)
            if lib.is_valid(n2, e2, d, D):
                cur_n, cur_e = n2, e2
                consider(cur_n, cur_e)
            continue
        adj = _sets_from_edges(cur_n, cur_e)
        color = _bipartition(cur_n, adj)
        _walk(cur_n, adj, color, D, rng, min(deadline, time.monotonic() + 2.0), 200)
        cur_e = [(a, b) for a in range(cur_n) for b in adj[a] if a < b]

    # Final verification of the best graph; fall back to K_{d,d} if anything is off.
    if lib.is_valid(best[0], best[1], d, D):
        return best
    return lib.haar_graph(d, range(d))

