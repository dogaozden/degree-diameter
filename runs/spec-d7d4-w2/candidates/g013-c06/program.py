import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
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


# ----------------------------------------------------------------------------
# New construction: Z_m voltage lifts of small bipartite base graphs.
#
# Base: k vertices on side A (ids 0..k-1) and k on side B (ids k..2k-1).
# Base edges are d colour classes; colour c is a permutation perms[c] matching
# a to k+perms[c][a], carrying voltage volt[c][a]. The lift has vertices u*m+g
# and joins a*m+g to b*m+(g+s)%m. Every lifted vertex has degree <= d.
# Diameter is checked by BFS from the 2k base sources (u, 0) only, since every
# other vertex of an orbit is a translate of these. Annealing minimises the
# number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _lift_nb(k, d, m, perms, volt):
    nb = [[] for _ in range(2 * k)]
    for c in range(d):
        for a in range(k):
            b = perms[c][a]
            s = volt[c][a]
            nb[a].append((k + b, s))
            nb[k + b].append((a, (-s) % m))
    return nb


def _lift_bad(k, m, nb, D):
    """Number of ordered (source, target) states not reachable within D from the base sources."""
    N = 2 * k * m
    total = 0
    for u in range(2 * k):
        seen = bytearray(N)
        s0 = u * m
        seen[s0] = 1
        frontier = [s0]
        cnt = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                uu, g = divmod(x, m)
                for w, t in nb[uu]:
                    y = w * m + (g + t) % m
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _lift_edges(k, d, m, perms, volt):
    edges = set()
    for c in range(d):
        for a in range(k):
            b = k + perms[c][a]
            s = volt[c][a]
            for g in range(m):
                edges.add((a * m + g, b * m + (g + s) % m))
    return sorted(edges)


def _anneal(k, d, m, D, rng, deadline):
    """Anneal a voltage/base assignment on m-lift until diameter <= D; return edges or None."""
    perms = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        perms.append(p)
    volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
    cur = _lift_bad(k, m, _lift_nb(k, d, m, perms, volt), D)
    temp = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        np_ = [p[:] for p in perms]
        nv = [v[:] for v in volt]
        c = rng.randrange(d)
        a = rng.randrange(k)
        if rng.random() < 0.7:
            nv[c][a] = rng.randrange(m)
        else:
            a2 = rng.randrange(k)
            np_[c][a], np_[c][a2] = np_[c][a2], np_[c][a]
        val = _lift_bad(k, m, _lift_nb(k, d, m, np_, nv), D)
        if val <= cur or rng.random() < math.exp(-(val - cur) / temp):
            perms, volt, cur = np_, nv, val
        temp = max(0.2, temp * 0.9995)
    return _lift_edges(k, d, m, perms, volt)


def _lift_phase(d, D, rng, deadline, consider, best):
    """Search voltage lifts with base sizes k = 2, 1, 3, growing m while annealing succeeds."""
    ks = (2, 1, 3)
    for idx, k in enumerate(ks):
        now = time.monotonic()
        if now >= deadline:
            break
        stop = now + (deadline - now) / (len(ks) - idx)
        m = best[0][0] // (2 * k) + 1
        while time.monotonic() < stop and m >= 2:
            e = _anneal(k, d, m, D, rng, stop)
            if e is None:
                break
            consider(2 * k * m, e)
            m += 1


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
# Twin blow-up with spare-capacity packing.
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
    """Choose candidates so that each resource u is used by at most cap[u] chosen candidates."""
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
    """Find candidates whose resource sets partition `universe` exactly (DFS, node-limited)."""
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
    """Twin as many vertices of one side as the spare degree of the other side allows."""
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
# Cover-based vertex extension.
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    end = start + 0.85 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    if D == 2:
        return best[0]
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best[0]
    if best[0][0] >= lib.moore_bound(d, D):
        return best[0]

    bases = []
    if D == 3:
        bases = _best_pg(d, 2)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    else:
        # Bold change for D >= 4: voltage-lift annealing over small base graphs
        # gets the first ~45% of the budget, before the W(q) expansion path.
        try:
            _lift_phase(d, D, rng, start + 0.45 * T, consider, best)
        except Exception:
            pass
        if best[0][0] >= lib.moore_bound(d, D):
            return best[0]
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= end:
                break
            try:
                bases.append(_gq_w(q))
            except Exception:
                pass

    for b in bases:
        consider(b[0], b[1])

    # Expansion from the bases; stop after repeated attempts that do not improve.
    rot = 0
    fails = 0
    while bases and time.monotonic() < end and fails < 8:
        if best[0][0] > 0 and rng.random() < 0.3:
            src = best[0]
        else:
            src = bases[rot % len(bases)]
            rot += 1
        before = best[0][0]
        try:
            n2, e2 = _expand(src[0], src[1], d, D, end, rng)
            consider(n2, e2)
        except Exception:
            break
        if best[0][0] == before:
            fails += 1

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0]
