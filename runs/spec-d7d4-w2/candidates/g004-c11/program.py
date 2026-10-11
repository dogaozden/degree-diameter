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
# NEW: non-abelian bi-Cayley (group-lift) search for D = 4.
#
# A base graph with one vertex per side and d darts (0, 1, s) lifts over a group G
# to the bi-Cayley graph a_x ~ b_{x*s}. Left multiplication is an automorphism
# that is transitive on each side, so diameter <= 4 only needs BFS from a_e and b_e.
# Simulated annealing over the connection set S minimises the number of unreached
# pairs. Groups are semidirect products Z_m x| Z_k (lib.semidirect_group).
# ----------------------------------------------------------------------------

def _group_candidates(lo, hi):
    """(order, m, k, r) for semidirect groups Z_m x| Z_k of each order in [lo, hi]."""
    out = []
    for N in range(max(lo, 2), hi + 1):
        for k in range(1, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            if k == 1:
                out.append((N, m, 1, 1))
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((N, m, k, r))
    return out


def _mul_table(m, k, r):
    """Return (order, mt, iv, mul) with mt[x][y] = x*y and iv[x] = x^{-1}; identity is index 0."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    mt = [[mul(x, y) for y in range(N)] for x in range(N)]
    iv = [inv(x) for x in range(N)]
    return N, mt, iv, mul


def _cost(S, mt, iv, N):
    """Number of vertex pairs (from a_e and b_e) at distance more than 4 in the bi-Cayley graph."""
    invS = [iv[s] for s in S]
    # BFS from a_e: A vertices reached at even depth, B at odd depth.
    seenA = {0}
    seenB = set()
    front = [0]
    for depth in range(4):
        nxt = []
        if depth % 2 == 0:
            for x in front:
                row = mt[x]
                for s in S:
                    y = row[s]
                    if y not in seenB:
                        seenB.add(y)
                        nxt.append(y)
        else:
            for y in front:
                row = mt[y]
                for si in invS:
                    x = row[si]
                    if x not in seenA:
                        seenA.add(x)
                        nxt.append(x)
        front = nxt
    cost = (N - len(seenA)) + (N - len(seenB))
    # BFS from b_e: covers B-B pairs (B vertices reached at even depth).
    seenB2 = {0}
    seenA2 = set()
    front = [0]
    for depth in range(4):
        nxt = []
        if depth % 2 == 0:
            for y in front:
                row = mt[y]
                for si in invS:
                    x = row[si]
                    if x not in seenA2:
                        seenA2.add(x)
                        nxt.append(x)
        else:
            for x in front:
                row = mt[x]
                for s in S:
                    y = row[s]
                    if y not in seenB2:
                        seenB2.add(y)
                        nxt.append(y)
        front = nxt
    cost += N - len(seenB2)
    return cost


def _anneal(N, mt, iv, d, rng, deadline, steps_per_restart=4000):
    """Find a d-subset S of the group with zero cost, or return None at the deadline."""
    if d > N:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        inS = set(S)
        c = _cost(S, mt, iv, N)
        if c == 0:
            return S
        T = 0.8
        for it in range(steps_per_restart):
            if (it & 63) == 0 and time.monotonic() > deadline:
                break
            i = rng.randrange(d)
            g = rng.randrange(N)
            if g in inS:
                continue
            old = S[i]
            S[i] = g
            c2 = _cost(S, mt, iv, N)
            delta = c2 - c
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                inS.discard(old)
                inS.add(g)
                c = c2
                if c == 0:
                    return list(S)
            else:
                S[i] = old
            T = max(0.15, T * 0.999)
    return None


def _group_search(d, D, rng, lo, hi, deadline, consider):
    """Search semidirect bi-Cayley lifts with 2N > current best order; feed successes to consider."""
    if D != 4 or lo > hi:
        return
    cands = _group_candidates(lo, hi)
    if not cands:
        return
    cur_lo = lo
    while time.monotonic() < deadline:
        pool = [c for c in cands if c[0] >= cur_lo]
        if not pool:
            break
        _, m, k, r = rng.choice(pool)
        slice_end = min(deadline, time.monotonic() + 4.0)
        Nn, mt, iv, mul = _mul_table(m, k, r)
        S = _anneal(Nn, mt, iv, d, rng, slice_end)
        if S is not None:
            n, edges = lib.group_lift(2, [(0, 1, s) for s in S], Nn, mul)
            consider(n, edges)
            cur_lo = Nn + 1


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
# Twin blow-up with spare-capacity packing (from the parent).
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
# Iterated local search with vertex excision and cover regrowth (from the parent).
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


def _ils(n, edges, d, D, deadline, rng, holder):
    """Iterated local search; holder[0] is the best verified (n, edges) so far."""
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rn <= 0:
            continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate_edges(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                continue
        rn, re = _fill(rn, re, d, D, rng, deadline)
        if rn >= cn:
            cn, ce = rn, re
            if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
                holder[0] = (rn, re)
    return


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _build_impl(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit
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

    bases = []
    if D == 3:
        bases = list(_best_pg(d, 2))
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= t0 + 0.2 * time_limit:
                break
            bases.append(_gq_w(q))

    for b in bases:
        consider(b[0], b[1])

    # Calibration shortcut: already at the Moore bound, nothing to gain.
    if best[0] >= lib._moore_bound(d, D):
        return best

    # Phase 1 (bold): non-abelian bi-Cayley lifts searched by annealing, for D = 4.
    if D == 4:
        hi = lib._moore_bound(d, D) // 2
        lo = best[0] // 2 + 1
        gs_deadline = t0 + 0.35 * time_limit
        try:
            _group_search(d, D, rng, lo, hi, gs_deadline, consider)
        except Exception:
            pass

    # Phase 2: expansion of the PG / GQ bases, then ILS on the best graph.
    now = time.monotonic()
    R = max(0.0, end - now)
    expand_deadline = now + 0.5 * R
    rot = 0
    while bases and time.monotonic() < expand_deadline:
        if best[0] > 0 and rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
        consider(n2, e2)

    if time.monotonic() < end and best[0] >= 2:
        holder = [best]
        _ils(best[0], best[1], d, D, end, rng, holder)
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    return best


def build(d, D, seed, time_limit):
    try:
        n, edges = _build_impl(d, D, seed, time_limit)
        if n == 1 and not edges:
            return n, edges
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    if D >= 2 and d >= 1:
        return lib.haar_graph(d, range(d))
    return 1, []
