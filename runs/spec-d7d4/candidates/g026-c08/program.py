import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
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


# ----------------------------------------------------------------------------
# Graph utilities.
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
# Twin blow-up with spare-capacity packing.
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


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

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

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
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
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
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
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    """Alternate twin packing on both sides with cover growth, while the graph keeps growing."""
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
# New construction: annealed voltage lifts over Z_m with p base vertices per side.
#
# Base graph: d perfect matchings between A = {a_0..a_{p-1}} and B = {b_0..b_{p-1}},
# matching k sends a_i to b_{pi_k(i)} with voltage volts[k][i] in Z_m.
# Lift: vertex (a_i, x) joins (b_j, x + s) for each matching. The lift is d-regular
# and bipartite with 2*p*m vertices. Translations by Z_m act transitively on each
# fibre, so the diameter is checked by BFS from one vertex per base vertex.
# ----------------------------------------------------------------------------

def _lift_adj(p, m, d, pis, volts):
    n = 2 * p * m
    adj = [[] for _ in range(n)]
    for k in range(d):
        pk = pis[k]
        vk = volts[k]
        for i in range(p):
            j = pk[i]
            s = vk[i]
            base_a = i * m
            base_b = p * m + j * m
            for x in range(m):
                a = base_a + x
                b = base_b + (x + s) % m
                adj[a].append(b)
                adj[b].append(a)
    return n, adj


def _lift_bad(p, m, d, D, pis, volts):
    """Number of (source, vertex) pairs at distance > D, summed over one source per base vertex."""
    n, adj = _lift_adj(p, m, d, pis, volts)
    sources = [i * m for i in range(p)] + [p * m + j * m for j in range(p)]
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nf = []
            for v in frontier:
                for u in adj[v]:
                    if not seen[u]:
                        seen[u] = 1
                        nf.append(u)
            if not nf:
                break
            cnt += len(nf)
            frontier = nf
        total += n - cnt
    return total


def _lift_edges(p, m, d, pis, volts):
    edges = set()
    for k in range(d):
        for i in range(p):
            j = pis[k][i]
            s = volts[k][i]
            for x in range(m):
                edges.add((i * m + x, p * m + j * m + (x + s) % m))
    return 2 * p * m, sorted(edges)


def _lift_search(p, m, d, D, deadline, rng):
    """Simulated annealing over matchings and voltages. Returns (pis, volts) or None."""
    pis = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        pis.append(perm)
    volts = [[rng.randrange(m) for _ in range(p)] for _ in range(d)]
    cur = _lift_bad(p, m, d, D, pis, volts)
    it = 0
    while cur > 0 and time.monotonic() < deadline:
        it += 1
        temp = max(0.3, 2.0 * (0.9995 ** it))
        k = rng.randrange(d)
        i = rng.randrange(p)
        if p == 1 or rng.random() < 0.75:
            old = volts[k][i]
            nv = rng.randrange(m)
            if nv == old:
                continue
            volts[k][i] = nv
            new = _lift_bad(p, m, d, D, pis, volts)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = new
            else:
                volts[k][i] = old
        else:
            j = rng.randrange(p)
            if j == i:
                continue
            pk = pis[k]
            pk[i], pk[j] = pk[j], pk[i]
            new = _lift_bad(p, m, d, D, pis, volts)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = new
            else:
                pk[i], pk[j] = pk[j], pk[i]
    if cur == 0:
        return pis, volts
    return None


def _lift_phase(consider, get_best_n, d, D, moore, deadline, rng):
    """Repeatedly try to beat the current best order with a lift of the next size up."""
    while time.monotonic() < deadline:
        bn = get_best_n()
        if bn >= moore:
            break
        tried = False
        for p in (1, 2, 3, 4):
            now = time.monotonic()
            if now >= deadline:
                break
            bn = get_best_n()
            m = -(-(bn + 1) // (2 * p))
            if m < 2 or 2 * p * m > moore:
                continue
            tried = True
            remaining = deadline - now
            slice_end = min(deadline, now + max(1.5, min(6.0, remaining / 4)))
            res = _lift_search(p, m, d, D, slice_end, rng)
            if res is not None:
                n, e = _lift_edges(p, m, d, res[0], res[1])
                consider(n, e)
        if not tried:
            break


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = [None]

    def consider(n, e):
        if best[0] is not None and n <= best[0][0]:
            return False
        if lib.is_valid(n, e, d, D):
            best[0] = (n, e)
            return True
        return False

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    hn, he = lib.haar_graph(d, range(d))
    consider(hn, he)
    if best[0] is None:
        return 1, []

    moore = lib._moore_bound(d, D)

    # Structured base: projective plane for D = 3, generalized quadrangle for D >= 4.
    base = None
    if D == 3:
        q = _largest_pp(d - 1)
        if q:
            base = lib.projective_plane_incidence(q)
    elif D >= 4:
        q = _largest_pp(min(d - 1, 7))
        if q:
            base = _gq_w(q)
    if base is not None:
        consider(base[0], base[1])
        sn, se = base[0], _saturate_edges(base[0], base[1], d, rng)
        consider(sn, se)

    if best[0][0] >= moore:
        return best[0]

    # Phase 1: cover/twin expansion of the structured base (the previous approach).
    if base is not None:
        deadA = start + 0.3 * total
        rounds = 0
        while time.monotonic() < deadA and rounds < 8:
            rounds += 1
            src = best[0] if (best[0] and rng.random() < 0.3) else base
            n2, e2 = _expand(src[0], src[1], d, D, deadA, rng)
            e2 = _saturate_edges(n2, e2, d, rng)
            consider(n2, e2)

    # Phase 2: annealed voltage lifts, aiming above the current best order.
    if best[0][0] < moore:
        _lift_phase(consider, lambda: best[0][0], d, D, moore, deadline, rng)

    return best[0]
