import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane and Araujo-Pardo-Lopez (D = 3).
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
# NEW: bit-parallel two-source diameter test for cyclic Haar graphs.
#
# The Haar graph H(Z_m, S) has vertices a_x, b_y (x, y in Z_m) with a_x ~ b_{x+s}
# for s in S. Z_m acts transitively on each side, and dist(a_i, b_j) equals
# dist(a_0, b_{j-i}). So diameter <= D holds iff a_0 and b_0 both reach every
# vertex within D steps. Each BFS level is a rotation of an m-bit integer, so
# one cost evaluation costs about 2*D*d big-int operations.
# ----------------------------------------------------------------------------

def _haar_unreached(m, S_pos, S_neg, D, full, src_side):
    """Vertices not reached within D steps from the source at position 0 on side src_side."""
    vis = [0, 0]
    vis[src_side] = 1
    frontier = 1
    side = src_side
    for _ in range(D):
        shifts = S_pos if side == 0 else S_neg
        nxt = 0
        for s in shifts:
            if s == 0:
                nxt |= frontier
            else:
                nxt |= (frontier << s) | (frontier >> (m - s))
        nxt &= full
        other = 1 - side
        nxt &= ~vis[other]
        vis[other] |= nxt
        frontier = nxt
        side = other
        if not frontier:
            break
    return 2 * m - vis[0].bit_count() - vis[1].bit_count()


def _haar_search(d, D, m, rng, deadline, iters):
    """Hill-climb S (|S| = d, 0 in S) so that H(Z_m, S) has diameter <= D; None on failure."""
    if m - 1 < d - 1:
        return None
    full = (1 << m) - 1

    def cost(S):
        neg = [(m - s) % m for s in S]
        return (_haar_unreached(m, S, neg, D, full, 0)
                + _haar_unreached(m, S, neg, D, full, 1))

    others = list(range(1, m))
    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 255) == 0 and time.monotonic() >= deadline:
            break
        cand = rng.randrange(1, m)
        if cand in S:
            continue
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = cand
        ct = cost(T)
        if ct <= c or rng.random() < 0.01:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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
    """Pairs (representative, vertex) not reached within D. Zero means valid."""
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


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _anneal(d, D, k, G, mul, rng, deadline, iters, start_darts=None, T0=1.0):
    """Simulated annealing over voltages and B-endpoints. Returns (edges_or_None, darts, cost)."""
    if start_darts is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start_darts]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = T0
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


# ----------------------------------------------------------------------------
# Double-edge-swap growth: add one vertex, anneal wiring with degree-preserving swaps.
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_ordered(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


_SWAP_ITER_CAP = 3200


def _swap_grow(n, edges, d, D, deadline, rng, max_fail=3, iters=200):
    if n < 2 or not edges:
        return n, list(edges)
    adj = _adj_sets(n, edges)
    color = _bipartition(n, adj)
    E = [((u, v) if color[u] == 0 else (v, u)) for u, v in edges]
    fails = 0
    cur_iters = iters
    while fails < max_fail and time.monotonic() < deadline:
        N = n + 1
        v = n
        adj2 = [set(s) for s in adj]
        adj2.append(set())
        E2 = list(E)
        color2 = list(color)
        c = rng.randrange(2)
        color2.append(c)

        opp = [x for x in range(n) if color[x] == 1 - c]
        rng.shuffle(opp)
        opp.sort(key=lambda x: len(adj2[x]))
        for b in opp[:d]:
            if len(adj2[b]) >= d:
                x = rng.choice(list(adj2[b]))
                adj2[b].discard(x)
                adj2[x].discard(b)
                e_rm = (b, x) if color2[b] == 0 else (x, b)
                E2.remove(e_rm)
            adj2[v].add(b)
            adj2[b].add(v)
            E2.append((b, v) if color2[b] == 0 else (v, b))

        def_a = [x for x in range(N) if color2[x] == 0 and len(adj2[x]) < d]
        def_b = [x for x in range(N) if color2[x] == 1 and len(adj2[x]) < d]
        pairs = [(a, b) for a in def_a for b in def_b if b not in adj2[a]]
        rng.shuffle(pairs)
        for a, b in pairs:
            if len(adj2[a]) < d and len(adj2[b]) < d and b not in adj2[a]:
                adj2[a].add(b)
                adj2[b].add(a)
                E2.append((a, b))

        cost = _bad_ordered(N, adj2, D)
        it = 0
        while cost and it < cur_iters and len(E2) >= 2 and time.monotonic() < deadline:
            it += 1
            i = rng.randrange(len(E2))
            j = rng.randrange(len(E2))
            a, b = E2[i]
            c2, e = E2[j]
            if a == c2 or b == e or e in adj2[a] or b in adj2[c2]:
                continue
            adj2[a].discard(b); adj2[b].discard(a)
            adj2[c2].discard(e); adj2[e].discard(c2)
            adj2[a].add(e); adj2[e].add(a)
            adj2[c2].add(b); adj2[b].add(c2)
            new = _bad_ordered(N, adj2, D)
            if new <= cost or rng.random() < 0.02:
                cost = new
                E2[i] = (a, e)
                E2[j] = (c2, b)
            else:
                adj2[a].discard(e); adj2[e].discard(a)
                adj2[c2].discard(b); adj2[b].discard(c2)
                adj2[a].add(b); adj2[b].add(a)
                adj2[c2].add(e); adj2[e].add(c2)

        if cost == 0 and all(len(s) <= d for s in adj2):
            n, adj, color, E = N, adj2, color2, E2
            fails = 0
            cur_iters = iters
        else:
            fails += 1
            cur_iters = min(cur_iters * 2, _SWAP_ITER_CAP)
    return n, [(a, b) for a, b in E]


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)
    hard = start + 0.90 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Phase 1 (NEW): cyclic Haar graphs with the bit-parallel two-source test.
    # Each success raises the lower bound for the next window of group orders.
    if D >= 3:
        haar_deadline = start + (0.35 if D >= 5 else 0.25) * time_limit
        while time.monotonic() < haar_deadline:
            lo = max(d + 1, best_n // 2 + 1)
            m = rng.randint(lo, lo + 40)
            S = _haar_search(d, D, m, rng, haar_deadline, 3000)
            if S is not None:
                n_h, e_h = lib.haar_graph(m, S)
                consider(n_h, e_h)

    # Phase 2: annealed non-cyclic voltage lifts (k base vertices per side).
    lift_deadline = start + (0.75 if D >= 5 else 0.5) * time_limit
    ks = [1, 1, 1, 2, 2, 3, 4]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    elite = {}
    while time.monotonic() < lift_deadline and D >= 3:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + (max(3, lo // 4) if k == 1 else max(3, lo // 8))
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng, k2_pool) if rng.random() < 0.8 else None
        if g is None:
            g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        key = (k, order)

        start_darts, T0, mul_use = None, 1.0, mul
        if key in elite and rng.random() < 0.5:
            _, st, mul_use = elite[key]
            start_darts = _perturb(st, order, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 1500 if k == 1 else 400
        res, darts_out, c = _anneal(d, D, k, order, mul_use, rng,
                                    lift_deadline, iters, start_darts, T0)
        if res is not None:
            consider(res[0], res[1])
            continue
        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use)

    # Phase 3: grow the best valid graph by vertex addition with swap annealing.
    if D >= 3 and best_n >= 2 and time.monotonic() < hard:
        max_fail = 10 ** 6 if D >= 5 else 3
        n_s, e_s = _swap_grow(best[0], best[1], d, D, hard, rng, max_fail=max_fail)
        consider(n_s, e_s)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
