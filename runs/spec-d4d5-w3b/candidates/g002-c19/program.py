import itertools
import math
import random
import time

import lib

BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Groups given by full multiplication tables: T[x][y] = x*y on 0..G-1.
# ----------------------------------------------------------------------------

def _cyc(m):
    return m, [[(x + y) % m for y in range(m)] for x in range(m)]


def _dih(m):
    # Dihedral group of order 2m; element 2*a+f means r^a s^f.
    T = []
    for x in range(2 * m):
        a, f = divmod(x, 2)
        row = []
        for y in range(2 * m):
            b, g = divmod(y, 2)
            na = (a + (b if f == 0 else -b)) % m
            row.append(2 * na + (f + g) % 2)
        T.append(row)
    return 2 * m, T


def _semi(m, k2, r):
    order, mulf, _ = lib.semidirect_group(m, k2, r)
    return order, [[mulf(x, y) for y in range(order)] for x in range(order)]


def _prod(A, B):
    GA, TA = A
    GB, TB = B
    G = GA * GB
    T = []
    for x in range(G):
        a1, b1 = divmod(x, GB)
        row = []
        for y in range(G):
            a2, b2 = divmod(y, GB)
            row.append(TA[a1][a2] * GB + TB[b1][b2])
        T.append(row)
    return G, T


def _random_group(lo, hi, rng):
    """Random group of order in [lo, hi] from several families, or None."""
    for _ in range(300):
        t = rng.random()
        if t < 0.2:
            return _cyc(rng.randint(lo, hi))
        if t < 0.4:
            m = rng.randint(max(2, lo // 2), hi // 2 + 1)
            if 2 <= m and lo <= 2 * m <= hi:
                return _dih(m)
            continue
        if t < 0.8:
            k2 = rng.randint(2, 12)
            m_lo = max(2, -(-lo // k2))
            m_hi = hi // k2
            if m_lo > m_hi:
                continue
            m = rng.randint(m_lo, m_hi)
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            return _semi(m, k2, rng.choice(cands))
        a = rng.randint(2, 12)
        b_lo = max(2, -(-lo // (2 * a)))
        b_hi = hi // (2 * a)
        if b_lo > b_hi:
            continue
        return _prod(_dih(a), _cyc(rng.randint(b_lo, b_hi)))
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over an arbitrary table group.
# Vertices A_{i,g} = i*G+g and B_{j,h} = (k+j)*G+h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s}. Each layer is a permutation
# of i -> j, so the lift is d-regular.
# ----------------------------------------------------------------------------

def _cost(k, G, D, darts, RT):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    seen = set()
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            return BIG
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        r = RT[s]
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + r[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
        mark = [False] * N
        mark[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not mark[v]:
                        mark[v] = True
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, darts, RT):
    E = set()
    for i, j, s in darts:
        r = RT[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + r[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, RT, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, RT)
    T0 = max(1.0, 0.05 * cost) if cost < BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, RT)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, RT)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, RT)
    return None


# ----------------------------------------------------------------------------
# Diameter-preserving growth: add a vertex whose neighbourhood covers the
# radius-(D-1) balls of everything, then saturate spare degree.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _greedy_cover(cands, ball, full, d, rng, shuffle):
    pool = list(cands)
    if shuffle:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best_i, best_g = -1, 0
        for i, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best_g:
                best_i, best_g = i, g
        if best_i < 0:
            break
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
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
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(5):
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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


def _grow(n, edges, d, D, deadline, rng):
    n2, e2 = _extend_cover(n, edges, d, D, deadline, rng)
    e2 = _saturate(n2, e2, d, rng)
    return n2, e2


# ----------------------------------------------------------------------------
# Projective plane base for D >= 3.
# ----------------------------------------------------------------------------

def _pg_base(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    pg = _pg_base(d)
    if pg is not None:
        consider(pg[0], pg[1])
        n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng)
        consider(n2, e2)

    # Main search: bi-Cayley lifts over varied table groups (order chosen just above
    # what the current best requires), with annealed voltages.
    ks = [1, 1, 2, 2, 3] if D >= 3 else [1, 2]
    iters = 1200
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        hi = lo + 8
        g = _random_group(lo, hi, rng)
        if g is None:
            continue
        G, T = g
        RT = [[T[x][s] for x in range(G)] for s in range(G)]
        local_deadline = min(deadline, time.monotonic() + 6.0)
        res = _anneal(d, D, k, G, RT, rng, local_deadline, iters)
        if res is not None:
            consider(res[0], res[1])
            gn, ge = _grow(res[0], res[1], d, D, deadline, rng)
            consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
