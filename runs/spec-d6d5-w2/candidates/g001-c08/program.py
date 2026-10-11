import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured starting graphs.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q), diameter 4, (q+1)-regular."""
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
# State handling for a d-regular bipartite graph stored as adjacency sets.
# Side 0 vertices and side 1 vertices are tracked explicitly.
# ----------------------------------------------------------------------------

def _to_state(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = [0 if v < n // 2 else 1 for v in range(n)]
    return adj, side


def _edges_of(nv, adj, side):
    return [(a, b) for a in range(nv) if side[a] == 0 for b in adj[a]]


def _bad(nv, adj, D):
    """Number of ordered vertex pairs at distance > D (bit-parallel). Zero iff connected with diameter <= D."""
    reach = [1 << v for v in range(nv)]
    for _ in range(D):
        new = [0] * nv
        for v in range(nv):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(nv - r.bit_count() for r in reach)


def _grow(nv, adj, side, d, rng):
    """Add one left vertex u and one right vertex w, keeping d-regularity.

    Pick a matching of d edges (a_t, b_t); delete them, join u to every b_t and w to every a_t.
    Returns the new vertex count, or None if no matching was found.
    """
    E = _edges_of(nv, adj, side)
    pick = None
    for _ in range(60):
        rng.shuffle(E)
        used_a, used_b, cur = set(), set(), []
        for a, b in E:
            if a not in used_a and b not in used_b:
                cur.append((a, b))
                used_a.add(a)
                used_b.add(b)
                if len(cur) == d:
                    break
        if len(cur) == d:
            pick = cur
            break
    if pick is None:
        return None
    u, w = nv, nv + 1
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    for a, b in pick:
        adj[a].discard(b)
        adj[b].discard(a)
    for a, b in pick:
        adj[u].add(b)
        adj[b].add(u)
        adj[a].add(w)
        adj[w].add(a)
    return nv + 2


def _replace(E, adj, i, new_i, j, new_j):
    """Replace edges E[i] and E[j] by new_i and new_j, keeping adjacency sets consistent."""
    a, b = E[i]
    c, e = E[j]
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    for x, y in (new_i, new_j):
        adj[x].add(y)
        adj[y].add(x)
    E[i] = new_i
    E[j] = new_j


def _anneal(nv, adj, side, D, d, deadline, rng, iters):
    """Degree-preserving double-edge swaps (simulated annealing) until the diameter is <= D.

    Returns True if a valid wiring was reached.
    """
    E = _edges_of(nv, adj, side)
    m = len(E)
    cur = _bad(nv, adj, D)
    if cur == 0:
        return True
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        T = 0.1 + 2.0 * (1.0 - it / iters)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        old_i, old_j = (a, b), (c, e)
        _replace(E, adj, i, (a, e), j, (c, b))
        new = _bad(nv, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            if cur == 0:
                return True
        else:
            _replace(E, adj, i, old_i, j, old_j)
    return cur == 0


# ----------------------------------------------------------------------------
# Main construction: grow a regular bipartite graph by one vertex pair at a time,
# re-annealing the wiring after every growth step.
# ----------------------------------------------------------------------------

_ITERS = 3000
_ATTEMPT_SECONDS = 6.0


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.82 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: order 2D, diameter D, optimal for d = 2
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    q = d - 1
    pg = lib.projective_plane_incidence(q) if (q >= 2 and lib.is_prime_power(q)) else None
    if pg is not None:
        consider(pg[0], pg[1])

    if D == 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # D >= 4: choose a regular, valid start to grow from.
    cands = []
    if 2 <= q <= 7 and lib.is_prime_power(q):
        try:
            cands.append(_gq_w(q))
        except Exception:
            pass
    if pg is not None:
        cands.append(pg)
    cands.append(best)
    start = next((c for c in cands if lib.is_valid(c[0], c[1], d, D)), best)
    consider(start[0], start[1])

    cur_n = start[0]
    cur_adj, cur_side = _to_state(start[0], start[1])
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        cand_adj = [set(s) for s in cur_adj]
        cand_side = list(cur_side)
        nn = _grow(cur_n, cand_adj, cand_side, d, rng)
        if nn is None:
            fails += 1
            continue
        att = min(deadline, time.monotonic() + _ATTEMPT_SECONDS)
        if _anneal(nn, cand_adj, cand_side, D, d, att, rng, _ITERS):
            cur_n, cur_adj, cur_side = nn, cand_adj, cand_side
            fails = 0
            if cur_n > best_n:
                consider(cur_n, _edges_of(cur_n, cur_adj, cur_side))
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
