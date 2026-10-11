import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers: colouring, state, bounded-diameter cost.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Bipartite Moore bound for max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _colour(n, edges):
    """Two-colouring of a bipartite graph (list of 0/1)."""
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


def _state(n, edges, colA):
    """Build (adj sets, E list of (a, b) with a on side A, pos index dict)."""
    adj = [set() for _ in range(n)]
    E = []
    pos = {}
    for u, v in edges:
        a, b = (u, v) if colA[u] else (v, u)
        if (a, b) in pos or a == b:
            continue
        adj[a].add(b)
        adj[b].add(a)
        pos[(a, b)] = len(E)
        E.append((a, b))
    return adj, E, pos


def _bad(n, adj, D):
    """Return (number of unordered pairs at distance > D, list of vertices with an unreached partner)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    full = (1 << n) - 1
    bad = [v for v in range(n) if ball[v] != full]
    cost = sum(n - ball[v].bit_count() for v in range(n)) // 2
    return cost, bad


# ----------------------------------------------------------------------------
# NEW: degree-preserving pair insertion followed by time-annealed 2-switch repair.
#
# Insertion: pick d edges (a_i, b_i) forming a matching. Delete them, add a new
# A-vertex x joined to all b_i and a new B-vertex y joined to all a_i. Every old
# vertex keeps its degree, x and y reach degree d, and bipartiteness holds.
#
# Repair: double-edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep every degree
# and bipartiteness. Anneal on the count of pairs at distance > D, with moves
# biased toward vertices that still have an unreached partner.
# ----------------------------------------------------------------------------

def _insert_pair(n, edges, colA, d, rng):
    """Insert one A-vertex and one B-vertex by rerouting a degree-d matching. Returns (n+2, edges, colA) or None."""
    order = list(range(len(edges)))
    rng.shuffle(order)
    ua, ub, chosen = set(), set(), []
    for idx in order:
        a, b = edges[idx]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    x, y = n, n + 1
    cset = set(chosen)
    new_edges = [e for k, e in enumerate(edges) if k not in cset]
    for idx in chosen:
        a, b = edges[idx]
        new_edges.append((a, y))
        new_edges.append((x, b))
    return n + 2, new_edges, list(colA) + [True, False]


def _swap(i, j, E, adj, pos):
    """Double-edge swap of E[i]=(p,q), E[j]=(r,s) into (p,s), (r,q). Self-inverse on the result."""
    p, q = E[i]
    r, s = E[j]
    adj[p].discard(q)
    adj[q].discard(p)
    adj[r].discard(s)
    adj[s].discard(r)
    adj[p].add(s)
    adj[s].add(p)
    adj[r].add(q)
    adj[q].add(r)
    del pos[(p, q)]
    del pos[(r, s)]
    E[i] = (p, s)
    E[j] = (r, q)
    pos[(p, s)] = i
    pos[(r, q)] = j


def _repair(n, adj, E, pos, D, end, rng):
    """Anneal double-edge swaps until every pair is within D or the deadline passes. True on success."""
    cost, bad = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= end:
            return False
        T = 1.0 * (0.03) ** ((now - t0) / span)
        if bad and rng.random() < 0.6:
            v = bad[rng.randrange(len(bad))]
            nb = rng.choice(tuple(adj[v]))
            i = pos.get((v, nb))
            if i is None:
                i = pos[(nb, v)]
        else:
            i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        p, q = E[i]
        r, s = E[j]
        if p == r or q == s or s in adj[p] or q in adj[r]:
            continue
        _swap(i, j, E, adj, pos)
        c2, bad2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, bad = c2, bad2
        else:
            _swap(i, j, E, adj, pos)
    return True


def _search_pairs(n, edges, colA, d, D, deadline, rng):
    """Repeatedly add a vertex pair and repair; keep successes. Returns the best valid (n, edges)."""
    moore = _moore(d, D)
    cur_n = n
    cur_e = [(a, b) if colA[a] else (b, a) for a, b in edges]
    cur_col = list(colA)
    best = (cur_n, cur_e)
    while time.monotonic() < deadline and cur_n + 2 <= moore:
        now = time.monotonic()
        remaining = deadline - now
        attempt_end = min(deadline, now + max(2.0, 0.35 * remaining))
        ins = _insert_pair(cur_n, cur_e, cur_col, d, rng)
        if ins is None:
            break
        n2, e2, col2 = ins
        adj, E, pos = _state(n2, e2, col2)
        if _repair(n2, adj, E, pos, D, attempt_end, rng):
            cur_n, cur_e, cur_col = n2, list(E), col2
            best = (cur_n, cur_e)
    return best


# ----------------------------------------------------------------------------
# Fallback: annealed group voltage lifts (used when no base construction applies).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _gcost(k, G, D, perms):
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for idx, pm in enumerate(perms):
        i, j = idx_block[idx]
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


idx_block = []


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Annealed search over voltages and block assignments for a bi-Cayley lift."""
    global idx_block
    darts = []
    idx_block = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
            idx_block.append((i, p[i]))
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return None
    cost = _gcost(k, G, D, perms)
    T = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T) ** (1.0 / max(1, iters)) if T > T_end else 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        new_s = rng.randrange(G)
        if new_s == old_s:
            continue
        old_perm = perms[idx]
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _gcost(k, G, D, perms)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm
    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _group_fallback(d, D, deadline, rng, best):
    best_n = best[0]
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, 400)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best = res
            best_n = res[0]
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    if D == 2:
        return best

    if D == 3:
        base = None
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            base = lib.projective_plane_incidence(d - 1)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                base = lib.araujo_lopez_graph(d - 2)
            except (ValueError, StopIteration, KeyError):
                base = None
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base
            colA = [c == 0 for c in _colour(base[0], base[1])]
            res = _search_pairs(base[0], base[1], colA, d, D, deadline, rng)
            if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
            return best
        best = _group_fallback(d, D, deadline, rng, best)
    else:
        best = _group_fallback(d, D, deadline, rng, best)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
