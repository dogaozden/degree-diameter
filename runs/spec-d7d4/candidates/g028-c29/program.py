import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley lifts over semidirect products Z_m x| Z_k.
#
# A base multigraph with p vertices per side (p = 1, 2, 3) and a d-regular
# bipartite dart pattern is lifted over a group G. Dart (i, j, g) joins
# a_{i,x} to b_{j, x*g} for every x in G. Left multiplication by G is an
# automorphism, so it suffices to check distances from the identity
# representatives a_{i,e} and b_{j,e} of every base vertex.
#
# The check is a batched numpy BFS over all 2p sources at once: the balls grow
# by scattering through permutation arrays x -> x*g, so one evaluation costs a
# few hundred microseconds. Zero unreached pairs means diameter <= D.
#
# Search: hill-climb over the group labels of the darts (for p = 1 the
# identity is fixed WLOG). The largest feasible |G| is found by bisection for
# each p, and every candidate is verified with lib.is_valid.
# The cyclic case (k = 1) reproduces the Haar-graph search as a special case.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [m for m in range(1, n + 1) if n % m == 0]


def _groups_of_order(N):
    """All semidirect products Z_m x| Z_k of order N, as (m, k, r) triples."""
    out = []
    for m in _divisors(N):
        k = N // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


class _Grp:
    """Semidirect product Z_m x| Z_k with cached right-multiplication permutations."""

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.N = m * k
        self.order, self.mul, _ = lib.semidirect_group(m, k, r)
        self.pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        xs = np.arange(self.N, dtype=np.int64)
        self.ca = xs // k
        self.cb = xs % k
        self.cache = {}

    def perm(self, g):
        """Return (P, Q): P[x] = x*g and Q = inverse permutation, Q[y] = y*g^{-1}."""
        hit = self.cache.get(g)
        if hit is None:
            c, dd = divmod(g, self.k)
            P = ((self.ca + self.pw[self.cb] * c) % self.m) * self.k + (self.cb + dd) % self.k
            Q = np.argsort(P)
            hit = (P, Q)
            self.cache[g] = hit
        return hit


def _bad(grp, slots, p, D):
    """Unreached (source, target) pairs for the lift; zero iff diameter <= D.

    Sources are a_{k,e} (index k) and b_{k,e} (index p+k) for each base vertex k.
    """
    N = grp.N
    K = 2 * p
    A = np.zeros((K, p, N), dtype=bool)
    B = np.zeros((K, p, N), dtype=bool)
    for k in range(p):
        A[k, k, 0] = True
        B[p + k, k, 0] = True
    ops = []
    for (i, j, g) in slots:
        P, Q = grp.perm(g)
        ops.append((i, j, P, Q))
    for _ in range(D):
        nA = A.copy()
        nB = B.copy()
        for i, j, P, Q in ops:
            nB[:, j, P] |= A[:, i, :]
            nA[:, i, Q] |= B[:, j, :]
        A, B = nA, nB
    total = int(A.sum()) + int(B.sum())
    return K * 2 * p * N - total


def _pattern(p, d, rng):
    """Base dart pattern: each row and column has exactly d darts (circulant-type shifts)."""
    shifts = [rng.randrange(p) for _ in range(d)]
    return [(i, (i + t) % p) for i in range(p) for t in shifts]


def _sa(grp, p, d, D, deadline, rng, iters=1500):
    """Simulated annealing over dart labels; returns (pattern, labels) with zero cost, or None."""
    N = grp.N
    while time.monotonic() < deadline:
        pat = _pattern(p, d, rng)
        L = len(pat)
        keyslots = {}
        for t, key in enumerate(pat):
            keyslots.setdefault(key, []).append(t)
        gs = [0] * L
        if p == 1:
            gs[0] = 0
            for t, x in zip(range(1, L), rng.sample(range(1, N), L - 1)):
                gs[t] = x
            movable = list(range(1, L))
        else:
            for key, ts in keyslots.items():
                for t, x in zip(ts, rng.sample(range(N), len(ts))):
                    gs[t] = x
            movable = list(range(L))
        cur = _bad(grp, [(pat[t][0], pat[t][1], gs[t]) for t in range(L)], p, D)
        T = 2.0
        for it in range(iters):
            if cur == 0:
                return pat, gs
            if it % 64 == 0 and time.monotonic() > deadline:
                return None
            t = movable[rng.randrange(len(movable))]
            key = pat[t]
            y = rng.randrange(N)
            if any(gs[u] == y for u in keyslots[key] if u != t):
                continue
            old = gs[t]
            gs[t] = y
            c2 = _bad(grp, [(pat[u][0], pat[u][1], gs[u]) for u in range(L)], p, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                gs[t] = old
            T = max(0.3, T * 0.9995)
    return None


def _test_N(N, p, d, D, deadline, rng):
    """Try to build a valid lift with |G| = N and p base vertices per side."""
    specs = _groups_of_order(N)
    if not specs:
        return None
    grps = [_Grp(m, k, r) for (m, k, r) in specs]
    rng.shuffle(grps)
    while time.monotonic() < deadline:
        for grp in grps:
            now = time.monotonic()
            if now >= deadline:
                break
            sub = min(deadline, now + 1.5)
            res = _sa(grp, p, d, D, sub, rng)
            if res is None:
                continue
            pat, gs = res
            darts = [(i, p + j, gs[t]) for t, (i, j) in enumerate(pat)]
            n, edges = lib.group_lift(2 * p, darts, N, grp.mul)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def _try(N, p, d, D, deadline, rng):
    try:
        r = _test_N(N, p, d, D, deadline, rng)
    except Exception:
        return None
    if r is not None and lib.is_valid(r[0], r[1], d, D):
        return r
    return None


def _bicayley_phase(best, d, D, moore, deadline, rng, slice_s):
    """For p = 1, 2, 3 bisect the largest feasible group order; keep the best valid graph."""
    weights = (0.5, 0.3, 0.2)
    for idx, p in enumerate((1, 2, 3)):
        now = time.monotonic()
        if now >= deadline or best[0] >= moore:
            break
        tail = sum(weights[idx:])
        p_deadline = now + (deadline - now) * weights[idx] / tail
        Nmax = moore // (2 * p)
        lo = max(d, best[0] // (2 * p) + 1)
        hi = Nmax
        if lo > hi:
            continue
        # Quick probe at the top of the range.
        r = _try(hi, p, d, D, min(p_deadline, time.monotonic() + 0.5), rng)
        if r is not None:
            if r[0] > best[0]:
                best = r
            lo = hi + 1
        while lo <= hi and time.monotonic() < p_deadline:
            mid = (lo + hi + 1) // 2
            slice_end = min(p_deadline, time.monotonic() + slice_s)
            r = _try(mid, p, d, D, slice_end, rng)
            if r is not None:
                if r[0] > best[0]:
                    best = r
                lo = mid + 1
            else:
                hi = mid - 1
        if best[0] >= moore:
            break
    return best


# ----------------------------------------------------------------------------
# Legacy pipeline, kept as a fallback for the remaining time.
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
# Driver: bi-Cayley lift search first, then the legacy pipeline with the
# remaining time. Every candidate is checked with lib.is_valid before it can
# replace the best.
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
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Phase 1: bi-Cayley lifts over semidirect products, bisection on the order.
    try:
        b2 = _bicayley_phase(best, d, D, moore, start + 0.55 * T, rng,
                             max(2.0, 0.05 * T))
        consider(b2[0], b2[1])
    except Exception:
        pass
    if best[0] >= moore:
        return best

    # Phase 2: legacy pipeline with the remaining time (it scales its own deadlines).
    remaining = start + 0.85 * T - time.monotonic()
    if remaining > 2.0:
        try:
            leg = _legacy_build(d, D, seed, remaining / 0.9)
        except Exception:
            leg = None
        if leg is not None:
            consider(leg[0], leg[1])

    return best
