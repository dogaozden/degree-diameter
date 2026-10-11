import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families for D = 3 (projective plane and Araujo-Pardo-Lopez).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bitmask reachability helpers.
# ----------------------------------------------------------------------------

def _adj_from(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _reach(n, adj, D):
    """Per vertex, a bitmask of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return reach


def _bad(reach, n):
    """Ordered count of (vertex, vertex) pairs at distance > D. Zero means valid."""
    return sum(n - r.bit_count() for r in reach)


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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = _adj_from(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _sample_group(G, rng, k2_choices=None):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = k2_choices or [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = _random_darts(d, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        reach = _reach(cur_n, _adj_from(cur_n, cur_e), D)
        bad = [cur_n - r.bit_count() for r in reach]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# NEW: targeted bad-pair switch repair.
#
# For a bad pair (u, w) on opposite sides, pick a random neighbour b of the left
# endpoint L and a random neighbour c of the right endpoint R, then replace
# (L,b), (c,R) by (L,R), (c,b). This is a 2-switch that gives the pair a direct
# edge, so it fixes the pair itself and keeps every degree and the bipartition.
# Moves that do not apply fall back to a random 2-switch. Accepted by Metropolis
# on the bad-pair count.
# ----------------------------------------------------------------------------

def _set_edge(adj, old, new):
    adj[old[0]].remove(old[1])
    adj[old[1]].remove(old[0])
    adj[new[0]].append(new[1])
    adj[new[1]].append(new[0])


def _repair_anneal(n, E, D, deadline, rng, T0=1.5):
    """Anneal targeted/random 2-switches to make the graph diameter <= D. Returns edges or None."""
    E = list(E)
    m = len(E)
    if m < 2:
        return None
    pos = {e: i for i, e in enumerate(E)}
    left = [False] * n
    for a, _ in E:
        left[a] = True
    adj = _adj_from(n, E)
    full = (1 << n) - 1
    reach = _reach(n, adj, D)
    cur = _bad(reach, n)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = max(0.05, T0 * (1.0 - (now - start) / span))
        bad_rows = [v for v in range(n) if reach[v] != full]
        u = rng.choice(bad_rows)
        missing = [w for w in range(n) if not (reach[u] >> w) & 1]
        w = rng.choice(missing)
        move = None
        if left[u] != left[w]:
            L, R = (u, w) if left[u] else (w, u)
            if adj[L] and adj[R]:
                b = rng.choice(adj[L])
                c = rng.choice(adj[R])
                if c != L and b != R and (c, b) not in pos:
                    move = ((L, b), (c, R), (L, R), (c, b))
        if move is None:
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or (a, e) in pos or (c, b) in pos:
                continue
            move = ((a, b), (c, e), (a, e), (c, b))
        old1, old2, new1, new2 = move
        i = pos[old1]
        j = pos[old2]
        del pos[old1]
        del pos[old2]
        E[i] = new1
        E[j] = new2
        pos[new1] = i
        pos[new2] = j
        _set_edge(adj, old1, new1)
        _set_edge(adj, old2, new2)
        reach2 = _reach(n, adj, D)
        c2 = _bad(reach2, n)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            reach = reach2
        else:
            del pos[new1]
            del pos[new2]
            E[i] = old1
            E[j] = old2
            pos[old1] = i
            pos[old2] = j
            _set_edge(adj, new1, old1)
            _set_edge(adj, new2, old2)
    return E


# ----------------------------------------------------------------------------
# Edge-splicing vertex insertion: add a left vertex x and a right vertex y of
# degree d each by splicing d edges, keeping all old degrees.
# ----------------------------------------------------------------------------

def _splice_pair(n, E, d, rng):
    m = len(E)
    if m < d:
        return None
    x, y = n, n + 1
    used, xs, ys, chosen = set(), set(), set(), []
    tries = 0
    while len(chosen) < d and tries < 50000:
        tries += 1
        i = rng.randrange(m)
        if i in used:
            continue
        a, b = E[i]
        if b in xs or a in ys:
            continue
        used.add(i)
        xs.add(b)
        ys.add(a)
        chosen.append(i)
    if len(chosen) < d:
        return None
    newE = [E[i] for i in range(m) if i not in used]
    for i in chosen:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    return n + 2, newE


def _splice_climb(n, E, d, D, deadline, rng, consider):
    cur_n, cur_E = n, E
    while time.monotonic() < deadline - 0.5:
        res = _splice_pair(cur_n, cur_E, d, rng)
        if res is None:
            break
        n2, E2 = res
        now = time.monotonic()
        att_end = min(deadline, now + max(2.0, (deadline - now) / 3.0))
        E3 = _repair_anneal(n2, E2, D, att_end, rng)
        if E3 is not None and consider(n2, E3):
            cur_n, cur_E = n2, E3


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    splice_ok = D >= 3 and d >= 3
    lift_end = min(deadline, start + (0.4 if splice_ok else 0.85) * time_limit)

    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] if D >= 5 else None

    while time.monotonic() < lift_end and best_n < moore:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        if k == 1 and D >= 5:
            hi = lo + max(3, lo // 4)
        else:
            hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)
        g = None
        if k2_pool is not None and rng.random() < 0.8:
            g = _sample_group(G, rng, k2_pool)
        if g is None:
            g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g

        iters = 1500 if k == 1 else 400
        res, darts_out, c = _anneal(d, D, k, order, mul, rng, lift_end, iters)
        if res is not None:
            consider(res[0], res[1])
            continue

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < lift_end:
            rep_deadline = min(lift_end, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, mul, darts_out, rep_deadline, rng)
            if out is not None:
                consider(out[0], out[1])

    # Targeted splice-and-repair growth from the best valid graph.
    if splice_ok and best_n < moore and time.monotonic() < deadline - 1.0:
        n0, e0 = best
        color0 = _bipartition(n0, _adj_from(n0, e0))
        E0 = [(u, v) if color0[u] == 0 else (v, u) for u, v in e0]
        _splice_climb(n0, E0, d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
