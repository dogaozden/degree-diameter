import itertools
import math
import random
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
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
# Cyclic / semidirect Haar graphs found by local search over the connection set.
#
# Group G = Z_m x| Z_k (order N). Haar graph: a_x ~ b_{x s} for s in S, |S| = d.
# Left translation is an automorphism, so diameter <= D iff the BFS from a_e and
# from b_e reaches everything within D steps.
# ----------------------------------------------------------------------------

def _group_list(N, rng, cap=10):
    """Candidate (m, k, r) with m * k = N giving semidirect products Z_m x| Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        rs = [r for r in range(m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        pick = rs if len(rs) <= 3 else rng.sample(rs, 3)
        for r in pick:
            out.append((m, k, r))
    rng.shuffle(out)
    return out[:cap]


def _group_tables(m, k, r):
    """Multiplication and inverse tables of the group in lib.semidirect_group coding; identity is 0."""
    r %= m
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    MUL = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    INV = ((-pw[nb] * a) % m) * k + nb
    if not np.array_equal(MUL[0], X):
        return None
    if not np.all(MUL[X, INV] == 0):
        return None
    return MUL, INV


def _haar_cost(MUL, S, negS, N, D):
    """Number of (vertex, start) pairs at distance > D from a_e and from b_e."""
    total = 0
    for start in (0, 1):
        A = np.zeros(N, dtype=bool)
        B = np.zeros(N, dtype=bool)
        if start == 0:
            A[0] = True
        else:
            B[0] = True
        for h in range(D):
            from_a = (start == 0) == (h % 2 == 0)
            if from_a:
                idx = np.flatnonzero(A)
                B[MUL[np.ix_(idx, S)].ravel()] = True
            else:
                idx = np.flatnonzero(B)
                A[MUL[np.ix_(idx, negS)].ravel()] = True
        total += 2 * N - int(A.sum()) - int(B.sum())
    return total


def _find_S(MUL, INV, N, d, D, deadline, rng, iters):
    """Hill-climb for a connection set S (|S| = d, containing identity 0) with diameter <= D."""
    def cost(Sl):
        arr = np.array(Sl, dtype=np.int64)
        return _haar_cost(MUL, arr, INV[arr], N, D)

    S = [0] + rng.sample(range(1, N), d - 1)
    c = cost(S)
    T = 1.0
    for it in range(iters):
        if c == 0:
            return S
        if it % 128 == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        y = rng.randrange(1, N)
        if y in S:
            continue
        S2 = list(S)
        S2[i] = y
        c2 = cost(S2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.2, T * 0.999)
    return S if c == 0 else None


def _haar_sweep(d, D, start_n, deadline, rng, per_n):
    """Find valid group Haar graphs of increasing order, starting above start_n."""
    if d < 2:
        return None
    lim = lib._moore_bound(d, D) // 2
    N = max(d, start_n // 2 + 1)
    best = None
    while N <= lim and time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + per_n)
        found = None
        for m, k, r in _group_list(N, rng):
            if time.monotonic() >= slice_end:
                break
            tabs = _group_tables(m, k, r)
            if tabs is None:
                continue
            MUL, INV = tabs
            S = _find_S(MUL, INV, N, d, D, slice_end, rng, 4000)
            if S is not None:
                found = (MUL, S)
                break
        if found is None:
            break
        MUL, S = found
        n2, e2 = lib.group_lift(2, [(0, 1, s) for s in S], N,
                                lambda x, y, M=MUL: int(M[x, y]))
        if not lib.is_valid(n2, e2, d, D):
            break
        best = (n2, e2)
        N += 1
    return best


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


def _saturated(n, edges, d, D, rng):
    """Use spare degree slots; kept only if the result verifies."""
    e2 = _saturate_edges(n, edges, d, rng)
    if len(e2) > len(edges) and lib.is_valid(n, e2, d, D):
        return (n, e2)
    return (n, edges)


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
# Simulated annealing vertex insertion (steal-attach moves on bad-pair count).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Driver.
# Order: base graph -> expansion -> group Haar sweep seeded above the current
# best -> spare-slot saturation -> annealed insertion. Every candidate is
# verified with lib.is_valid before it can replace the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    exp_end = start + 0.30 * T
    haar_end = start + 0.62 * T
    anneal_end = start + 0.86 * T
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

    bases = []
    try:
        if D == 3:
            b = _best_pg(d)
            if b is not None:
                bases.append(b)
        elif D >= 4:
            qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
            for q in qs:
                if time.monotonic() >= exp_end:
                    break
                bases.append(_gq_w(q))
    except Exception:
        bases = []

    for b in bases:
        consider(b[0], b[1])
    if best[0] >= moore:
        return best

    # Phase 1: expansion from bases and from the current best.
    try:
        rot = 0
        while bases and time.monotonic() < exp_end:
            if best[0] > 0 and rng.random() < 0.3:
                src = best
            else:
                src = bases[rot % len(bases)]
                rot += 1
            n2, e2 = _expand(src[0], src[1], d, D, exp_end, rng)
            consider(n2, e2)
    except Exception:
        pass

    # Phase 2: cyclic and semidirect Haar graphs, seeded above the current best order.
    try:
        per_n = max(1.0, 0.04 * T)
        r = _haar_sweep(d, D, best[0], haar_end, rng, per_n)
        if r is not None:
            consider(r[0], r[1])
    except Exception:
        pass
    if best[0] >= moore:
        return best

    # Phase 3: use spare slots, then annealed vertex insertion.
    try:
        if best[0] >= 2:
            best = _saturated(best[0], best[1], d, D, rng)
        while best[0] >= 2 and time.monotonic() < anneal_end:
            slice_end = min(anneal_end, time.monotonic() + 4.0)
            res = _anneal_add(best[0], best[1], d, D, slice_end, rng)
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = _saturated(res[0], res[1], d, D, rng)
    except Exception:
        pass

    return best
