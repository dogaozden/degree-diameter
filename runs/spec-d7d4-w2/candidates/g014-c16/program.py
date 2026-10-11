"""Parent pipeline plus a new routine: Haar-graph search over finite groups.

New idea (not used by the parent): a bipartite Haar graph over a group G of
order N has vertices a_x, b_x (x in G) with a_x ~ b_{x*s} for s in a connection
set S of size d. Left multiplication by h is an automorphism, so the diameter is
checked with just two BFS runs (from a_e and b_e) over 2N vertices. A simulated
annealing search over the d-element set S then looks for a connection set with
diameter <= D. Groups are cyclic Z_N or semidirect products Z_m x| Z_k. The
search starts just above the parent's order, so it only adds graphs that beat it.
Every result is still verified with lib.is_valid, and the best valid graph wins.
"""
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


def _bad(n, adj, D):
    return sum(n - b.bit_count() for b in _balls_radius(n, adj, D)) // 2


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
# Cover-based vertex extension (diameter-preserving growth).
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
# Iterated local search: vertex excision, saturation repair, cover regrowth.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    """Delete vertex x; the last vertex takes its label. Returns (n-1, edges)."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
    """Add one vertex by a degree-respecting cover; return (n+1, edges) or None."""
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
    """Repeatedly add cover vertices while possible, then saturate spare slots."""
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


def _move(cn, ce, d, D, rng, deadline, targeted):
    """Excise one vertex, repair the diameter if cheaply possible, then refill."""
    if targeted:
        best_x, best_b = None, None
        for _ in range(6):
            x = rng.randrange(cn)
            n2, e2 = _remove_vertex(cn, ce, x)
            b = _bad(n2, _adjacency(n2, e2), D)
            if best_b is None or b < best_b:
                best_x, best_b = x, b
        x = best_x
    else:
        x = rng.randrange(cn)
    rn, re = _remove_vertex(cn, ce, x)
    if rn <= 1:
        return None
    if not lib.within_diameter(rn, re, D):
        re = _saturate_edges(rn, re, d, rng)
        if not lib.within_diameter(rn, re, D):
            return None
    return _fill(rn, re, d, D, rng, deadline)


def _ils(n, edges, d, D, deadline, rng, holder):
    """Iterated local search; holder[0] is the best verified (n, edges) so far."""
    cn, ce = n, list(edges)
    stale = 0
    while time.monotonic() < deadline:
        if stale > 400:
            cn, ce = holder[0][0], list(holder[0][1])
            stale = 0
        cand = _move(cn, ce, d, D, rng, deadline, rng.random() < 0.4)
        if cand is None:
            stale += 1
            continue
        rn, re = cand
        if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
            holder[0] = (rn, re)
            cn, ce = rn, re
            stale = 0
            continue
        stale += 1
        floor = holder[0][0] - 2
        if rn >= cn or (rn == cn - 1 and rn >= floor and rng.random() < 0.05):
            cn, ce = rn, re


# ----------------------------------------------------------------------------
# NEW: Haar graphs over finite groups, found by annealing the connection set.
#
# Group G of order N, connection set S of d distinct elements.
# Vertices a_x = x, b_x = N + x; a_x ~ b_{x*s} for s in S (degree d, bipartite).
# Left multiplication by h is an automorphism, so pairs reduce to sources a_e and
# b_e: two BFS runs suffice. The cost is the number of vertices farther than D
# from both sources. Annealing over S drives the cost to 0.
# ----------------------------------------------------------------------------

def _groups_of_order(N, rng, limit=16):
    """Cyclic group Z_N and semidirect products Z_m x| Z_k (m*k = N), as (order, mul, inv)."""
    cands = [lib.cyclic_group(N)]
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    cands.append(lib.semidirect_group(m, k, r))
                except ValueError:
                    pass
    rng.shuffle(cands)
    return cands[:limit]


def _tables(group):
    """Multiplication table and inverse list for a group (order, mul, inv)."""
    order, mul, inv = group
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    iv = [inv(x) for x in range(order)]
    return mt, iv


def _haar_cost(S, N, D, mt, iv):
    """Number of (source, vertex) pairs at distance > D from a_e or b_e (0 means diameter <= D)."""
    Sinv = [iv[s] for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = mt[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = mt[v - N]
                    for t in Sinv:
                        w = row[t]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - reached
    return total


def _haar_anneal(N, d, D, mt, iv, rng, deadline, max_evals):
    """Anneal a connection set S of size d; return S with cost 0, or None."""
    S = rng.sample(range(N), d)
    cur = _haar_cost(S, N, D, mt, iv)
    temp = 1.5
    evals = 0
    while cur > 0 and evals < max_evals and time.monotonic() < deadline:
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        S2 = S[:]
        S2[i] = t
        c2 = _haar_cost(S2, N, D, mt, iv)
        evals += 1
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            S, cur = S2, c2
        temp = max(0.2, temp * 0.9995)
    return S if cur == 0 else None


def _haar_edges(N, S, mt):
    """Edges of the Haar graph: a_x ~ b_{x*s}."""
    return 2 * N, [(x, N + mt[x][s]) for x in range(N) for s in S]


def _haar_search(d, D, N0, Nmax, rng, deadline):
    """Find the smallest-first Haar graphs with N >= N0 (each with 2N vertices), stopping at the first failure."""
    best = None
    N = N0
    while N <= Nmax and time.monotonic() < deadline:
        groups = _groups_of_order(N, rng)
        if not groups:
            break
        cache = {}
        found = None
        found_mt = None
        gi = 0
        while time.monotonic() < deadline and found is None:
            idx = gi % len(groups)
            gi += 1
            if idx not in cache:
                cache[idx] = _tables(groups[idx])
            mt, iv = cache[idx]
            chunk_end = min(deadline, time.monotonic() + 4.0)
            found = _haar_anneal(N, d, D, mt, iv, rng, chunk_end, 6000)
            if found is not None:
                found_mt = mt
        if found is None:
            break
        n, e = _haar_edges(N, found, found_mt)
        if lib.is_valid(n, e, d, D):
            best = (n, e)
        N += 1
    return best


# ----------------------------------------------------------------------------
# Parent pipeline (unchanged logic, now run with a share of the time budget).
# ----------------------------------------------------------------------------

def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    expand_deadline = start + 0.30 * T
    search_deadline = start + 0.85 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    # Calibration shortcut: already at the Moore bound, nothing to gain.
    if best[0] >= lib.moore_bound(d, D):
        return best

    bases = []
    if D == 3:
        bases = _best_pg(d, 2)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    else:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= expand_deadline:
                break
            try:
                bases.append(_gq_w(q))
            except Exception:
                pass

    for b in bases:
        consider(b[0], b[1])

    rot = 0
    fails = 0
    while bases and time.monotonic() < expand_deadline and fails < 8:
        if best[0] > 0 and rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        before = best[0]
        try:
            n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
            consider(n2, e2)
        except Exception:
            break
        if best[0] == before:
            fails += 1

    if best[0] >= lib.moore_bound(d, D):
        return best
    if time.monotonic() < search_deadline and best[0] >= 2:
        holder = [best]
        try:
            _ils(best[0], best[1], d, D, search_deadline, rng, holder)
        except Exception:
            pass
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)

    if d < 1 or D < 1:
        return 1, []

    # Parent pipeline gets about half the budget; the Haar search gets the rest.
    best = _parent_build(d, D, seed, 0.5 * T)

    if D < 2 or d < 3:
        return best
    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Haar search: only orders N with 2N > current best, up to Moore/2.
    N0 = best[0] // 2 + 1
    Nmax = moore // 2
    if N0 > Nmax or N0 < d:
        return best

    deadline = start + 0.85 * T
    rng = random.Random(seed + 12345)
    try:
        hb = _haar_search(d, D, max(N0, d), Nmax, rng, deadline)
    except Exception:
        hb = None

    if hb is not None and hb[0] > best[0] and lib.is_valid(hb[0], hb[1], d, D):
        best = hb
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
