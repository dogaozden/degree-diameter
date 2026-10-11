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


# ----------------------------------------------------------------------------
# NEW: group-lift search over (possibly non-abelian) groups.
#
# A base bipartite multigraph on a + a vertices is d-regular (d random perfect
# matchings). Each dart (u, v, g) is lifted over a group G of order N:
# (u, x) ~ (v, x*g). Left multiplication is an automorphism, so the lift has
# diameter <= D iff every base vertex's fibre representative (u, identity) has
# eccentricity <= D. The cost is the number of far vertices from these 2a
# representatives, and simulated annealing lowers it by re-drawing voltages.
# ----------------------------------------------------------------------------

def _group_specs(N):
    """Specs for groups of order N: cyclic, and semidirect Z_m x| Z_k with m*k = N."""
    specs = [("c", N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                specs.append(("s", m, k, r))
    return specs


def _make_group(spec):
    """Return (order, mt) where mt[x][y] = x*y in the group; identity is element 0."""
    if spec[0] == "c":
        N, mul, _ = lib.cyclic_group(spec[1])
    else:
        N, mul, _ = lib.semidirect_group(spec[1], spec[2], spec[3])
    mt = [[mul(x, y) for y in range(N)] for x in range(N)]
    return N, mt


def _lift_configs(lo, hi, rng):
    """Candidate (n, a, group spec) with n = 2*a*N in [lo, hi]."""
    cfgs = []
    for a in range(1, 7):
        for N in range(max(2, -(-lo // (2 * a))), hi // (2 * a) + 1):
            n = 2 * a * N
            if n < lo or n > hi:
                continue
            for spec in _group_specs(N):
                cfgs.append((n, a, spec))
    rng.shuffle(cfgs)
    return cfgs[:12]


def _random_darts(a, d, N, rng):
    """d random perfect matchings between the A side (0..a-1) and B side (a..2a-1)."""
    darts = []
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            darts.append([i, a + perm[i], rng.randrange(N)])
    return darts


def _lift_adj(a, N, mt, darts):
    adj = [[] for _ in range(2 * a * N)]
    for u, v, g in darts:
        for x in range(N):
            p = u * N + x
            q = v * N + mt[x][g]
            adj[p].append(q)
            adj[q].append(p)
    return adj


def _lift_cost(a, N, D, adj):
    """Total number of vertices not within distance D of the 2a fibre representatives."""
    nn = len(adj)
    total = 0
    for u in range(2 * a):
        src = u * N
        dist = [-1] * nn
        dist[src] = 0
        frontier = [src]
        reached = 1
        for depth in range(1, D + 1):
            nxt = []
            for p in frontier:
                for q in adj[p]:
                    if dist[q] < 0:
                        dist[q] = depth
                        nxt.append(q)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += nn - reached
    return total


def _lift_edges(a, N, mt, darts):
    es = set()
    for u, v, g in darts:
        for x in range(N):
            p = u * N + x
            q = v * N + mt[x][g]
            if p != q:
                es.add((min(p, q), max(p, q)))
    return sorted(es)


def _sa_chunk(a, st, d, D, rng, t_end, T=0.7):
    """Anneal voltages for one configuration until t_end; True when a zero-cost lift is found."""
    N, mt = st['N'], st['mt']
    while time.monotonic() < t_end:
        darts = st['darts']
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        darts[idx][2] = rng.randrange(N)
        c = _lift_cost(a, N, D, _lift_adj(a, N, mt, darts))
        if c <= st['cost'] or rng.random() < math.exp(-(c - st['cost']) / T):
            if c < st['cost']:
                st['stale'] = 0
            else:
                st['stale'] += 1
            st['cost'] = c
            if c == 0:
                return True
        else:
            darts[idx][2] = old
            st['stale'] += 1
        if st['stale'] > 3000:
            st['darts'] = _random_darts(a, d, N, rng)
            st['cost'] = _lift_cost(a, N, D, _lift_adj(a, N, mt, st['darts']))
            st['stale'] = 0
    return False


def _lift_search(d, D, lo, hi, deadline, rng):
    """Round-robin annealing over lift configurations; returns the largest valid (n, edges) found."""
    cfgs = _lift_configs(lo, hi, rng)
    if not cfgs:
        return None
    states = [None] * len(cfgs)
    done = [False] * len(cfgs)
    found = None
    cur = lo - 1
    while time.monotonic() < deadline:
        active = [i for i, (n, a, spec) in enumerate(cfgs) if not done[i] and n > cur]
        if not active:
            break
        chunk = max(0.4, (deadline - time.monotonic()) / (3.0 * len(active)))
        for i in active:
            now = time.monotonic()
            if now >= deadline:
                break
            n, a, spec = cfgs[i]
            if done[i] or n <= cur:
                continue
            if states[i] is None:
                N, mt = _make_group(spec)
                darts = _random_darts(a, d, N, rng)
                cost = _lift_cost(a, N, D, _lift_adj(a, N, mt, darts))
                states[i] = {'N': N, 'mt': mt, 'darts': darts, 'cost': cost, 'stale': 0}
            st = states[i]
            t_end = min(deadline, now + chunk)
            if _sa_chunk(a, st, d, D, rng, t_end):
                done[i] = True
                nn = 2 * a * st['N']
                edges = _lift_edges(a, st['N'], st['mt'], st['darts'])
                if nn > cur and lib.is_valid(nn, edges, d, D):
                    found = (nn, edges)
                    cur = nn
    return found


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


def _ils(n, edges, d, D, deadline, rng, holder, stall_limit=300):
    """Iterated local search; holder[0] is the best verified (n, edges) so far."""
    cn, ce = n, list(edges)
    stall = 0
    while time.monotonic() < deadline:
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rn <= 0:
            continue
        if rng.random() < 0.2:
            y = rng.randrange(rn)
            rn, re = _remove_vertex(rn, re, y)
            if rn <= 0:
                continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate_edges(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                stall += 1
                continue
        rn, re = _fill(rn, re, d, D, rng, deadline)
        if rn >= cn:
            if rn > cn:
                stall = 0
            cn, ce = rn, re
            if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
                holder[0] = (rn, re)
                stall = 0
        else:
            stall += 1
        if stall > stall_limit:
            cn, ce = holder[0][0], list(holder[0][1])
            stall = 0
    return


# ----------------------------------------------------------------------------
# Driver.
#
# Change: a group-lift annealing phase (non-cyclic groups, base multigraphs of
# up to 12 vertices) runs first on the 38% time slice, targeting orders above the
# current best. The parent's expansion and ILS then run on the remaining budget,
# starting from the best graph found so far. The safe fallback is K_{d,d}, and every
# candidate passes lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    lift_deadline = start + 0.38 * time_limit
    expand_deadline = start + 0.50 * time_limit
    search_deadline = start + 0.90 * time_limit
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
        bases = [b for b in _best_pg(d, 2)]
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= expand_deadline:
                break
            bases.append(_gq_w(q))

    for b in bases:
        consider(b[0], b[1])

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Phase 0: group-lift annealing for orders above the current best.
    lo = best[0] + 1
    hi = min(moore, int(best[0] * 1.25) + 8)
    if lo <= hi and time.monotonic() < lift_deadline:
        cand = _lift_search(d, D, lo, hi, lift_deadline, rng)
        if cand is not None:
            consider(cand[0], cand[1])

    # Phase 1: parent expansion from bases (and from the best graph).
    rot = 0
    while bases and time.monotonic() < expand_deadline:
        if best[0] > 0 and rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
        consider(n2, e2)

    # Phase 2: iterated local search on the best graph found.
    if time.monotonic() < search_deadline and best[0] >= 2:
        holder = [best]
        _ils(best[0], best[1], d, D, search_deadline, rng, holder)
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    return best
