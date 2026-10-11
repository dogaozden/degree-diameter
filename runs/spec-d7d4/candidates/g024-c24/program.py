import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Phase 1: cyclic Haar graphs H(m, S) with local search over the shift set S.
# (Unchanged from the parent: a single-orbit voltage lift with 1 base vertex per side.)
# ----------------------------------------------------------------------------

def _spread(X, shifts, m, full):
    """Union of the rotations of bitmask X by each shift in `shifts` (mod m)."""
    R = 0
    for s in shifts:
        R |= ((X << s) | (X >> (m - s))) & full
    return R


def _reach_bad(m, S, negS, D, full, start_side):
    """Number of vertices NOT within D of a source (a_0 if start_side == 0, else b_0)."""
    if start_side == 0:
        A, B = 1, 0
    else:
        A, B = 0, 1
    for h in range(D):
        if (h % 2 == 0) == (start_side == 0):
            B |= _spread(A, S, m, full)
        else:
            A |= _spread(B, negS, m, full)
    return (m - A.bit_count()) + (m - B.bit_count())


def _cost(m, S, D, full):
    negS = [(m - s) % m for s in S]
    return _reach_bad(m, S, negS, D, full, 0) + _reach_bad(m, S, negS, D, full, 1)


def _find_shifts(m, d, D, deadline, rng):
    """Hill-climb with restarts for a shift set S (containing 0) of size d giving diameter <= D."""
    full = (1 << m) - 1
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        c = _cost(m, S, D, full)
        T = 2.0
        for it in range(30000):
            if c == 0:
                return sorted(S)
            if it % 200 == 0 and time.monotonic() > deadline:
                return None
            k = rng.randrange(1, d)
            y = rng.randrange(1, m)
            if y in S:
                continue
            S2 = S.copy()
            S2[k] = y
            c2 = _cost(m, S2, D, full)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c = S2, c2
            T = max(0.3, T * 0.9997)
    return None


def _haar_search(d, D, deadline, rng, per):
    """Increase m while a valid cyclic Haar graph is found. Returns (n, edges) or None."""
    if d < 2:
        return None
    moore = lib._moore_bound(d, D)
    m = d
    best = None
    while m <= moore // 2 and time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + per)
        S = _find_shifts(m, d, D, slice_end, rng)
        if S is None:
            break
        best = (m, S)
        m += 1
    if best is None:
        return None
    return lib.haar_graph(best[0], best[1])


# ----------------------------------------------------------------------------
# Phase 2 (new idea): multi-orbit voltage lifts.
#
# Base multigraph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, with d
# random perfect matchings between A and B, so every base vertex has degree d.
# Each base dart (i, j) carries a voltage a in Z_m. The lift has 2*k*m vertices:
# A_i,x ~ B_j,(x+a) for every x in Z_m. It is d-regular (up to duplicate darts,
# which are merged and only lower degree) and bipartite by construction.
#
# Diameter check: the lift is Z_m-invariant, so the lift has diameter <= D iff
# from each of the 2k sources (base vertex, 0) every lifted vertex is within D.
# Reach sets are bitmasks over Z_m, and a dart moves a set by a rotation. The
# cost is the number of ordered unreached (source, vertex) pairs, which is 0 iff
# the lift is valid. Simulated annealing changes one voltage at a time. Unlike
# the single-orbit Haar search, the extra base vertices give orders 2km that
# land between the Haar sizes.
# ----------------------------------------------------------------------------

def _mo_cost(k, m, D, darts, full):
    """Total unreached ordered pairs, summed over the 2k base sources."""
    K2 = 2 * k
    inn = [[] for _ in range(K2)]
    for i, j, a in darts:
        # from A_i at x -> B_j at x+a ; from B_j at y -> A_i at y-a
        inn[k + j].append((i, a))
        inn[i].append((k + j, (m - a) % m))
    total = 0
    for s in range(K2):
        R = [0] * K2
        R[s] = 1
        for _ in range(D):
            newR = []
            for w in range(K2):
                x = R[w]
                for u, sh in inn[w]:
                    Ru = R[u]
                    x |= ((Ru << sh) | (Ru >> (m - sh))) & full
                newR.append(x)
            R = newR
        for w in range(K2):
            total += m - R[w].bit_count()
    return total


def _mo_edges(k, m, darts):
    edges = set()
    for i, j, a in darts:
        for x in range(m):
            edges.add((i * m + x, k * m + j * m + (x + a) % m))
    return 2 * k * m, sorted(edges)


def _mo_search(k, d, D, m, deadline, rng, restart=12000):
    """Anneal voltages for a random d-regular k+k base multigraph lifted over Z_m.

    Returns (n, edges) with diameter <= D, or None if the deadline passes first.
    """
    if m < 2 or 2 * k * m > lib._moore_bound(d, D):
        return None
    full = (1 << m) - 1
    while time.monotonic() < deadline:
        base = []
        for _ in range(d):
            perm = list(range(k))
            rng.shuffle(perm)
            for i in range(k):
                base.append((i, perm[i]))
        darts = [(i, j, rng.randrange(m)) for i, j in base]
        c = _mo_cost(k, m, D, darts, full)
        T = 1.0
        for it in range(restart):
            if c == 0:
                break
            if it % 64 == 0 and time.monotonic() > deadline:
                return None
            e = rng.randrange(len(darts))
            i, j, a = darts[e]
            na = rng.randrange(m)
            if na == a:
                continue
            darts[e] = (i, j, na)
            c2 = _mo_cost(k, m, D, darts, full)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
            else:
                darts[e] = (i, j, a)
            T = max(0.2, T * 0.9995)
        if c == 0:
            return _mo_edges(k, m, darts)
    return None


def _offer(holder, n, e, d, D):
    """Replace holder[0] with (n, e) if it is larger and passes the exact checker."""
    if n > holder[0][0] and lib.is_valid(n, e, d, D):
        holder[0] = (n, e)


def _multi_phase(d, D, deadline, rng, holder, moore, per):
    """Climb the orders 2*k*m for k = 2 and k = 3, one slice per attempt."""
    mcur = {}
    while time.monotonic() < deadline:
        for k in (2, 3):
            m = max(holder[0][0] // (2 * k) + 1, mcur.get(k, 0))
            if 2 * k * m > moore:
                continue
            mcur[k] = m
            slice_end = min(deadline, time.monotonic() + per)
            res = _mo_search(k, d, D, m, slice_end, rng)
            if res is not None:
                _offer(holder, res[0], res[1], d, D)
                mcur[k] = m + 1
            if time.monotonic() >= deadline:
                return


# ----------------------------------------------------------------------------
# Legacy pipeline (previous parent), kept as a fallback and for the remaining time.
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
        if holder[0][0] > cn and rng.random() < 0.002:
            cn, ce = holder[0][0], list(holder[0][1])
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rn <= 0:
            continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate_edges(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                continue
        rn, re = _fill(rn, re, d, D, rng, deadline)
        if rn >= cn or (rn == cn - 1 and rng.random() < 0.05):
            cn, ce = rn, re
            if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
                holder[0] = (rn, re)
    return


def _sets_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_sets(N, adj, D):
    """Number of unordered pairs at distance > D, from adjacency sets."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _apply(adj, op):
    kind, a, b = op
    if kind == 'add':
        adj[a].add(b)
        adj[b].add(a)
    else:
        adj[a].discard(b)
        adj[b].discard(a)


def _undo(adj, op):
    kind, a, b = op
    if kind == 'add':
        adj[a].discard(b)
        adj[b].discard(a)
    else:
        adj[a].add(b)
        adj[b].add(a)


def _greedy_partial(cands, ball, d):
    """Pick up to d candidates greedily by coverage gain; full cover not required."""
    pool = list(cands)
    covered = 0
    chosen = []
    while pool and len(chosen) < d:
        best_i = max(range(len(pool)),
                     key=lambda i: (ball[pool[i]] & ~covered).bit_count())
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]
    return chosen


def _anneal_add(n, edges, d, D, deadline, rng, T0=0.8):
    """Try to insert one more vertex by annealing its neighbourhood. Returns (n+1, edges) or None."""
    if n < 2 or not edges:
        return None
    adj_lists = _adjacency(n, edges)
    color = _bipartition(n, adj_lists)
    deg = [len(a) for a in adj_lists]
    c = rng.randrange(2)
    opp = [x for x in range(n) if color[x] == 1 - c]
    if not opp:
        return None

    ball = _balls_radius(n, adj_lists, D - 1)
    cands = [s for s in opp if deg[s] < d]
    rng.shuffle(cands)
    init = _greedy_partial(cands, ball, d) if cands else []

    adj = _sets_from_edges(n, edges)
    v = n
    N = n + 1
    adj.append(set())
    for s in init:
        adj[v].add(s)
        adj[s].add(v)

    cur = _bad_sets(N, adj, D)
    it = 0
    while time.monotonic() < deadline:
        if cur == 0:
            new_edges = [(a, b) for a in range(N) for b in adj[a] if a < b]
            if lib.is_valid(N, new_edges, d, D):
                return N, new_edges
            return None
        it += 1
        t = opp[rng.randrange(len(opp))]
        if t in adj[v]:
            continue
        ops = []
        if len(adj[v]) >= d:
            s = rng.choice(tuple(adj[v]))
            ops.append(('del', v, s))
        if len(adj[t]) >= d:
            u = rng.choice(tuple(adj[t]))
            ops.append(('del', t, u))
        ops.append(('add', v, t))
        for op in ops:
            _apply(adj, op)
        new = _bad_sets(N, adj, D)
        delta = new - cur
        T = max(0.05, T0 * (0.999 ** it))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            for op in reversed(ops):
                _undo(adj, op)
    return None


def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    expand_deadline = start + 0.35 * time_limit
    ils_deadline = start + 0.70 * time_limit
    anneal_deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bases = []
    if D == 3:
        bases = [b for b in _best_pg(d, 2)]
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= expand_deadline:
                break
            bases.append(_gq_w(q))

    for b in bases:
        consider(b[0], b[1])

    if best[0] >= lib._moore_bound(d, D):
        return best

    rot = 0
    while bases and time.monotonic() < expand_deadline:
        if best[0] > 0 and rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
        consider(n2, e2)

    if time.monotonic() < ils_deadline and best[0] >= 2:
        holder = [best]
        _ils(best[0], best[1], d, D, ils_deadline, rng, holder)
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    while best[0] >= 2 and time.monotonic() < anneal_deadline:
        slice_end = min(anneal_deadline, time.monotonic() + 4.0)
        res = _anneal_add(best[0], best[1], d, D, slice_end, rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    return best


# ----------------------------------------------------------------------------
# Driver: cyclic Haar search, then multi-orbit voltage lifts, then the legacy
# pipeline with the remaining time. Every candidate is checked with lib.is_valid
# before it can replace the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    holder = [lib.haar_graph(d, range(d))]
    moore = lib._moore_bound(d, D)
    if holder[0][0] >= moore:
        return holder[0]

    # Phase 1: cyclic Haar graphs (short budget).
    per1 = max(2.0, 0.05 * T)
    try:
        r = _haar_search(d, D, start + 0.10 * T, rng, per1)
    except Exception:
        r = None
    if r is not None:
        _offer(holder, r[0], r[1], d, D)
    if holder[0][0] >= moore:
        return holder[0]

    # Phase 2 (new): multi-orbit voltage lifts with annealed voltages.
    if d >= 3 and D >= 2:
        per2 = max(1.0, 0.06 * T)
        try:
            _multi_phase(d, D, start + 0.55 * T, rng, holder, moore, per2)
        except Exception:
            pass
    if holder[0][0] >= moore:
        return holder[0]

    # Phase 3: legacy pipeline with the remaining time (it scales its own deadlines).
    remaining = start + 0.85 * T - time.monotonic()
    if remaining > 2.0:
        try:
            leg = _legacy_build(d, D, seed, remaining / 0.9)
        except Exception:
            leg = None
        if leg is not None:
            _offer(holder, leg[0], leg[1], d, D)

    return holder[0]
