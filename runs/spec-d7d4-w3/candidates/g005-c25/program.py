"""Pair-insertion annealing for bipartite graphs with max degree d and diameter D.

New idea (not in the parent): a degree-preserving vertex-pair insertion. Pick d-1
disjoint edges (a_i, b_i), replace each by (a_i, y) and (x, b_i), then add the edge
(x, y). This adds two vertices x (side 0) and y (side 1) while keeping every existing
degree and bipartiteness. The diameter then breaks, so a simulated-annealing search
over degree-preserving double-edge swaps repairs it, with the number of pairs at
distance > D as the cost. Each success grows the graph by two vertices.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
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
    edges = []
    nlines = 0
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
            for p in L:
                edges.append((p, P + nlines))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nlines += 1
    return 2 * P, edges


def _largest_pp(hi):
    for q in range(hi, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _base(d, D):
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d}, Moore-optimal for D = 2
    if D == 3:
        q = _largest_pp(d - 1)
        if q is None:
            return None
        return lib.projective_plane_incidence(q)
    q = _largest_pp(min(d - 1, 7))
    if q is None:
        return None
    return _gq_w(q)


# ----------------------------------------------------------------------------
# State: adjacency sets, edge list (side-0 endpoint first), sides.
# ----------------------------------------------------------------------------

def _to_state(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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
    E = [((u, v) if color[u] == 0 else (v, u)) for u, v in edges]
    return {"n": n, "adj": adj, "E": E, "side": color}


def _copy(st):
    return {"n": st["n"], "adj": [set(s) for s in st["adj"]],
            "E": list(st["E"]), "side": list(st["side"])}


def _saturate(st, d, rng):
    """Greedily add edges between opposite-side vertices with spare degree (keeps diameter)."""
    n, adj, side, E = st["n"], st["adj"], st["side"], st["E"]
    left = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))


def _insert_pair(st, d, rng):
    """Degree-preserving insertion of a new adjacent pair (x on side 0, y on side 1)."""
    adj, E, side = st["adj"], st["E"], st["side"]
    if d < 2 or len(E) < d - 1:
        return False
    idx = list(range(len(E)))
    rng.shuffle(idx)
    ua, ub, chosen = set(), set(), []
    for i in idx:
        a, b = E[i]
        if a in ua or b in ub:
            continue
        chosen.append(i)
        ua.add(a)
        ub.add(b)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return False
    x = st["n"]
    y = x + 1
    st["n"] += 2
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    for i in chosen:
        a, b = E[i]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(y)
        adj[y].add(a)
        adj[x].add(b)
        adj[b].add(x)
        E[i] = (a, y)
        E.append((x, b))
    adj[x].add(y)
    adj[y].add(x)
    E.append((x, y))
    return True


# ----------------------------------------------------------------------------
# Cost and annealing.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(n - b.bit_count() for b in ball) // 2


def _anneal(st, D, deadline, rng, T0=2.0, T1=0.2):
    """Degree-preserving double-edge swaps, Metropolis acceptance, until cost 0 or deadline."""
    n, adj, E = st["n"], st["adj"], st["E"]
    m = len(E)
    cost = _bad(n, adj, D)
    if m < 2:
        return cost
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            cost = c2
        else:
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
    return cost


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.2 * time_limit, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    base = _base(d, D)
    if base is None:
        return best
    bn, be = base
    consider(bn, be)
    if bn >= moore:
        return best

    cur = _to_state(bn, be)
    _saturate(cur, d, rng)
    if _bad(cur["n"], cur["adj"], D) > 0:
        _anneal(cur, D, deadline, rng)
    if _bad(cur["n"], cur["adj"], D) > 0:
        return best
    consider(cur["n"], cur["E"])

    attempt_slice = max(2.0, 0.08 * time_limit)
    while time.monotonic() < deadline - 0.5:
        if cur["n"] + 2 > moore:
            break
        trial = _copy(cur)
        if not _insert_pair(trial, d, rng):
            break
        slice_end = min(deadline, time.monotonic() + attempt_slice)
        c = _anneal(trial, D, slice_end, rng)
        if c == 0:
            cur = trial
            consider(cur["n"], cur["E"])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
