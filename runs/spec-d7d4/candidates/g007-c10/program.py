import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# NEW (bold): bi-Cayley graphs over small groups.
# Vertices (0, g) and (1, h), g, h in G. Edge (0, g) -- (1, g*s) for s in S, |S| = d.
# Left multiplication is an automorphism acting transitively on each side, so the
# diameter is decided by two BFS runs, from (0, e) and from (1, e).
# Groups are Z_a x|_r Z_b (lib.semidirect_group), order a*b = G.
# ----------------------------------------------------------------------------

def _group_tables(a, b, r):
    order, mul, inv = lib.semidirect_group(a, b, r)
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    iv = [inv(x) for x in range(order)]
    return order, mt, iv


def _groups_of_order(G, rng):
    out = []
    for b in range(1, G + 1):
        if G % b:
            continue
        a = G // b
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        rng.shuffle(rs)
        for r in rs[:6]:
            out.append((a, b, r))
    return out


def _bc_cost(G, S, mt, iv, D):
    """Number of (source, vertex) pairs not within distance D; zero iff diameter <= D."""
    N = 2 * G
    adj = [None] * N
    for g in range(G):
        row = mt[g]
        adj[g] = [G + row[s] for s in S]
    for h in range(G):
        row = mt[h]
        adj[G + h] = [row[iv[s]] for s in S]
    cost = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        cost += N - cnt
    return cost


def _bc_search_group(G, mt, iv, d, D, rng, deadline, restarts, iters):
    for _ in range(restarts):
        if time.monotonic() > deadline:
            return None
        S = rng.sample(range(G), d)
        cost = _bc_cost(G, S, mt, iv, D)
        for _ in range(iters):
            if cost == 0 or time.monotonic() > deadline:
                break
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            old = S[i]
            S[i] = x
            c2 = _bc_cost(G, S, mt, iv, D)
            if c2 <= cost:
                cost = c2
            else:
                S[i] = old
        if cost == 0:
            return list(S)
    return None


def _bc_try_order(G, d, D, rng, deadline):
    groups = _groups_of_order(G, rng)
    rng.shuffle(groups)
    for a, b, r in groups:
        if time.monotonic() > deadline:
            break
        _, mt, iv = _group_tables(a, b, r)
        S = _bc_search_group(G, mt, iv, d, D, rng, deadline, 3, 150)
        if S is not None:
            return S, mt
    return None


def _bc_edges(G, S, mt):
    edges = []
    for g in range(G):
        row = mt[g]
        for s in S:
            edges.append((g, G + row[s]))
    return 2 * G, edges


def _bicayley_phase(d, D, deadline, rng, consider, st):
    G_hi = lib._moore_bound(d, D) // 2
    while time.monotonic() < deadline:
        G_lo = max(st["best"][0] // 2 + 1, d)
        if G_lo > G_hi:
            break
        G = G_lo + rng.randrange(4)
        if G > G_hi:
            G = G_lo
        chunk = min(deadline, time.monotonic() + 4.0)
        res = _bc_try_order(G, d, D, rng, chunk)
        if res is not None:
            S, mt = res
            n2, e2 = _bc_edges(G, S, mt)
            consider(n2, e2)


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


def _extend_cover(n, edges, d, D, deadline, rng):
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


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(20):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
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


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000, 30000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Exact-cover growth: a new vertex whose neighbourhood covers all vertices within D-1.
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
# Search phases.
# ----------------------------------------------------------------------------

def _expansion_loop(d, D, seed, deadline, bases, consider, st):
    if not bases:
        return
    attempt = 0
    rot = 0
    while time.monotonic() < deadline:
        attempt += 1
        arng = random.Random(seed * 1000003 + attempt)
        if arng.random() < 0.4:
            src = st["best"]
        else:
            src = bases[rot % len(bases)]
            rot += 1
        if arng.random() < 0.5:
            n2, e2 = _polish(src[0], src[1], d, D, deadline, arng)
        else:
            n2, e2 = _expand(src[0], src[1], d, D, deadline, arng)
        e2 = _saturate_edges(n2, e2, d, arng)
        consider(n2, e2)


def _run(d, D, seed, start, total, deadline, rng, consider, st):
    if D == 2:
        return  # K_{d,d} already has the Moore order 2d for D = 2

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # even cycle C_{2D}

    if D == 3:
        pg = _best_pg(d)
        if pg is None:
            return
        consider(pg[0], pg[1])
        _expansion_loop(d, D, seed, deadline, [pg], consider, st)
        return

    if D >= 4:
        bases = _gq_bases(d, 2)
        for b in bases:
            consider(b[0], b[1])
        if not bases:
            return
        # Phase 1: expansion of the generalized-quadrangle bases.
        _expansion_loop(d, D, seed, start + 0.3 * total, bases, consider, st)
        # Phase 2 (bold): bi-Cayley search over groups, targeting beyond the current best.
        _bicayley_phase(d, D, start + 0.75 * total, rng, consider, st)
        # Phase 3: expansion again, from the best graph found so far and the bases.
        _expansion_loop(d, D, seed + 1, deadline, bases, consider, st)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    st = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    try:
        _run(d, D, seed, start, total, deadline, rng, consider, st)
    except Exception:
        pass
    return st["best"]
