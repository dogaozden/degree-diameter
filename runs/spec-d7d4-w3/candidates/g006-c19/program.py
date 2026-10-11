import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d, count=1):
    """Incidence graphs of PG(2, q) for the largest prime powers q with q + 1 <= d."""
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


def _gq_bases(d, count):
    out = []
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            out.append(_gq_w(q))
            if len(out) == count:
                break
    return out


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


def _balls_radius(n, adj, r):
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


# ----------------------------------------------------------------------------
# NEW: Cayley-type bipartite (Haar-type) graphs over small groups.
#
# Vertices A_g and B_g for g in G; A_g ~ B_{g s} for s in S, |S| = d.
# Left multiplication by h is an automorphism, so the diameter condition only
# needs to be checked from A_e and B_e. Each check is a tiny BFS, which makes
# hill-climbing over connection sets S fast.
# ----------------------------------------------------------------------------

def _group_specs(m):
    """(a, b, r) with Z_a x| Z_b of order m = a*b, valid for lib.semidirect_group."""
    specs = []
    for b in range(1, m + 1):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                specs.append((a, b, r))
    return specs


def _group_tables(a, b, r):
    order, mul, inv = lib.semidirect_group(a, b, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    Iv = [inv(x) for x in range(order)]
    return order, M, Iv


def _cayley_cost(M, Iv, S, m, D):
    """Number of (source, vertex) pairs at distance > D, summed over sources A_e and B_e."""
    Sinv = [Iv[s] for s in S]
    total = 0
    for start in (0, 1):
        seen = (bytearray(m), bytearray(m))
        seen[start][0] = 1
        frontier = [0]
        count = 1
        side = start
        for _ in range(D):
            nxt = []
            if side == 0:
                for g in frontier:
                    row = M[g]
                    for s in S:
                        y = row[s]
                        if not seen[1][y]:
                            seen[1][y] = 1
                            nxt.append(y)
            else:
                for x in frontier:
                    row = M[x]
                    for t in Sinv:
                        y = row[t]
                        if not seen[0][y]:
                            seen[0][y] = 1
                            nxt.append(y)
            count += len(nxt)
            frontier = nxt
            side ^= 1
            if not frontier:
                break
        total += 2 * m - count
    return total


def _cayley_search(M, Iv, m, d, D, rng, deadline, iters):
    if d > m:
        return None
    S = rng.sample(range(m), d)
    cost = _cayley_cost(M, Iv, S, m, D)
    T = 1.0
    for it in range(iters):
        if cost == 0:
            return S
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cayley_cost(M, Iv, S, m, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
    return S if cost == 0 else None


def _cayley_graph(M, m, S):
    edges = []
    for g in range(m):
        row = M[g]
        for s in S:
            edges.append((g, m + row[s]))
    return 2 * m, edges


def _cayley_try(m, d, D, rng, end, iters):
    specs = _group_specs(m)
    if not specs:
        return None
    rng.shuffle(specs)
    tries = specs[:4]
    for idx, (a, b, r) in enumerate(tries):
        now = time.monotonic()
        if now >= end:
            break
        left = len(tries) - idx
        share = (end - now) / max(1, left)
        try:
            order, M, Iv = _group_tables(a, b, r)
        except ValueError:
            continue
        S = _cayley_search(M, Iv, order, d, D, rng, now + share, iters)
        if S is not None:
            return order, M, S
    return None


def _cayley_phase(d, D, seed, end, consider):
    """Binary-search the largest order m with a valid Cayley bipartite graph of order 2m."""
    moore = lib._moore_bound(d, D)
    hi_m = moore // 2
    lo_m = max(d + 1, int(0.55 * hi_m))
    if hi_m - lo_m < 2:
        return None
    rng = random.Random(seed * 1009 + 17 * d + D)
    best = [None]

    def test(m, budget_end, iters):
        res = _cayley_try(m, d, D, rng, budget_end, iters)
        if res is None:
            return False
        order, M, S = res
        n, e = _cayley_graph(M, order, S)
        if not lib.is_valid(n, e, d, D):
            return False
        if best[0] is None or n > best[0][0]:
            best[0] = (n, e)
        consider(n, e)
        return True

    lo, hi = lo_m, hi_m + 1
    if not test(lo, min(end, time.monotonic() + 4.0), 4000):
        return best[0]
    while hi - lo > 1:
        now = time.monotonic()
        if now >= end:
            break
        mid = (lo + hi) // 2
        if test(mid, min(end, now + 2.5), 4000):
            lo = mid
        else:
            hi = mid
    m = lo + 1
    while m <= hi_m and time.monotonic() < end:
        now = time.monotonic()
        if test(m, min(end, now + 6.0), 6000):
            lo = m
            m += 1
        else:
            break
    return best[0]


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover-based vertex addition, edge saturation.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    attempts_max = 600 if D >= 4 else 200

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts_max):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       always_random or attempt > 0)
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


def _saturate_edges(n, edges, d, rng):
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(12):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing (valid for D >= 2).
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
    k = len(R)
    if k == 0:
        return []
    users = [[] for _ in range(n)]
    for i, r in enumerate(R):
        for u in r:
            users[u].append(i)
    load = [0] * n
    inS = [False] * k
    S = set()

    def add(i):
        inS[i] = True
        S.add(i)
        for u in R[i]:
            load[u] += 1

    def remove(i):
        inS[i] = False
        S.discard(i)
        for u in R[i]:
            load[u] -= 1

    order = list(range(k))
    rng.shuffle(order)
    for i in order:
        if all(load[u] < cap[u] for u in R[i]):
            add(i)
    best = list(S)

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        i = rng.randrange(k)
        if inS[i]:
            continue
        removed = []
        for u in R[i]:
            while load[u] >= cap[u]:
                j = rng.choice([x for x in users[u] if inS[x]])
                remove(j)
                removed.append(j)
        add(i)
        delta = 1 - len(removed)
        if delta < 0 and rng.random() >= 0.03:
            remove(i)
            for j in removed:
                add(j)
        if len(S) > len(best):
            best = list(S)
    return best


def _exact_cover(R, universe, users, deadline, node_cap):
    covered = set()
    chosen = []
    nodes = [0]

    def rec():
        if len(covered) == len(universe):
            return True
        nodes[0] += 1
        if nodes[0] > node_cap or time.monotonic() > deadline:
            return False
        best_opts = None
        for u in universe:
            if u in covered:
                continue
            opts = [i for i in users[u] if all(r not in covered for r in R[i])]
            if not opts:
                return False
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        for i in best_opts:
            for r in R[i]:
                covered.add(r)
            chosen.append(i)
            if rec():
                return True
            chosen.pop()
            for r in R[i]:
                covered.discard(r)
        return False

    return list(chosen) if rec() else None


def _twin_pass(n, edges, d, side, rng, deadline, iters):
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    capv = [d - deg[u] for u in range(n)]
    cands = [v for v in range(n)
             if color[v] == side and adj[v] and all(capv[u] >= 1 for u in adj[v])]
    if not cands:
        return n, edges
    R = [adj[v] for v in cands]
    universe = sorted({u for r in R for u in r})

    chosen = None
    if all(capv[u] == 1 for u in universe):
        users = [[] for _ in range(n)]
        for i, r in enumerate(R):
            for u in r:
                users[u].append(i)
        ex = _exact_cover(R, universe, users, deadline, 3000)
        if ex is not None:
            chosen = ex
    pk = _pack(R, capv, n, rng, deadline, iters)
    if chosen is None or len(pk) > len(chosen):
        chosen = pk
    if not chosen:
        return n, edges

    new_edges = list(edges)
    nn = n
    for i in chosen:
        v = cands[i]
        for u in adj[v]:
            new_edges.append((u, nn))
        nn += 1
    return nn, new_edges


def _expand(n, edges, d, D, deadline, rng, rounds=6, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000, 30000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng, always_random)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Cover search growth and polishing.
# ----------------------------------------------------------------------------

def _cover_search(ball, cands, full, d, rng, budget):
    used = set()
    chosen = []
    nodes = [0]

    def rec(covered, depth):
        if covered == full:
            return True
        if depth >= d or nodes[0] >= budget:
            return False
        nodes[0] += 1
        rem = full & ~covered
        free = [s for s in cands if s not in used]
        gains = {s: (ball[s] & rem).bit_count() for s in free}
        best = max(gains.values(), default=0)
        if best == 0 or rem.bit_count() > best * (d - depth):
            return False
        bits = []
        x = rem
        while x:
            low = x & -x
            bits.append(low.bit_length() - 1)
            x ^= low
        sample = rng.sample(bits, min(6, len(bits)))
        best_opts = None
        for w in sample:
            opts = [s for s in free if gains[s] and (ball[s] >> w) & 1]
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        if not best_opts:
            return False
        rng.shuffle(best_opts)
        best_opts.sort(key=lambda s: -gains[s])
        for s in best_opts:
            used.add(s)
            chosen.append(s)
            if rec(covered | ball[s], depth + 1):
                return True
            used.discard(s)
            chosen.pop()
            if nodes[0] >= budget:
                break
        return False

    return list(chosen) if rec(0, 0) else None


def _grow_exact(n, edges, d, D, deadline, rng, budget):
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            if not cands:
                continue
            chosen = _cover_search(ball, cands, full, d, rng, budget)
            if chosen:
                v = n
                n += 1
                color.append(c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                placed = True
                break
        if not placed:
            break
    return n, edges


def _polish(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(3):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        cur_n, cur_e = _grow_exact(cur_n, cur_e, d, D, deadline, rng, 1500)
        cur_e = _saturate_edges(cur_n, cur_e, d, rng)
        for side in (0, 1):
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, 10000)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        cur_e = _saturate_edges(cur_n, cur_e, d, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Iterated local search with vertex excision and cover regrowth.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen = None
        for attempt in range(30):
            chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                break
        if chosen:
            v = n
            new_edges = list(edges)
            for s in chosen:
                new_edges.append((s, v))
            return n + 1, new_edges
    return None


def _fill(n, edges, d, D, rng, deadline):
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


def _ils(n, edges, d, D, deadline, rng, holder):
    """Iterated local search; holder[0] is the best verified (n, edges) so far."""
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rng.random() < 0.2 and rn > 1:
            y = rng.randrange(rn)
            rn, re = _remove_vertex(rn, re, y)
        if rn <= 0:
            continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate_edges(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                continue
        rn, re = _fill(rn, re, d, D, rng, deadline)
        accept = rn >= cn or (rn >= holder[0][0] - 2 and rng.random() < 0.05)
        if accept:
            cn, ce = rn, re
            if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
                holder[0] = (rn, re)


# ----------------------------------------------------------------------------
# Search phases.
# ----------------------------------------------------------------------------

def _expansion_loop(d, D, seed, deadline, bases, consider, st):
    if not bases:
        return
    target = lib._moore_bound(d, D)
    attempt = 0
    rot = 0
    while time.monotonic() < deadline and st["best"][0] < target:
        attempt += 1
        arng = random.Random(seed * 1000003 + attempt)
        if arng.random() < 0.35:
            src = st["best"]
        else:
            src = bases[rot % len(bases)]
            rot += 1
        always_random = arng.random() < 0.3
        if arng.random() < 0.5:
            n2, e2 = _polish(src[0], src[1], d, D, deadline, arng)
        else:
            n2, e2 = _expand(src[0], src[1], d, D, deadline, arng,
                             always_random=always_random)
        e2 = _saturate_edges(n2, e2, d, arng)
        consider(n2, e2)


def _final_ils(d, D, deadline, rng, st):
    if time.monotonic() >= deadline or st["best"][0] < 2:
        return
    holder = [st["best"]]
    _ils(st["best"][0], st["best"][1], d, D, deadline, rng, holder)
    if holder[0][0] > st["best"][0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
        st["best"] = holder[0]


def _run(d, D, seed, start, total, deadline, rng, consider, st):
    if D == 2:
        return  # K_{d,d} already has the Moore order 2d for D = 2

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # even cycle C_{2D}
        return

    moore = lib._moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d, 2)
        for b in pg:
            consider(b[0], b[1])
        if not pg or st["best"][0] >= moore:
            return
        _expansion_loop(d, D, seed, start + 0.6 * total, list(pg), consider, st)
        _final_ils(d, D, deadline, rng, st)
        return

    # D >= 4
    bases = _gq_bases(d, 2)
    for b in bases:
        consider(b[0], b[1])
    if st["best"][0] >= moore:
        return
    try:
        cay = _cayley_phase(d, D, seed, start + 0.5 * total, consider)
    except Exception:
        cay = None
    if cay is not None:
        bases.append(cay)
    if not bases:
        return
    _expansion_loop(d, D, seed, start + 0.9 * total, bases, consider, st)
    _final_ils(d, D, deadline, rng, st)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    st = {"best": lib.haar_graph(d, range(d))}  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    if st["best"][0] < lib._moore_bound(d, D):
        try:
            _run(d, D, seed, start, total, deadline, rng, consider, st)
        except Exception:
            pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
