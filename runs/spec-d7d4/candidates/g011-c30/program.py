import itertools
import math
import random
import time

import numpy as np

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
# Twin blow-up with spare-capacity packing (inherited from the parent).
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
# Cover-based vertex extension (inherited from the parent).
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
# NEW: group-Haar graphs searched by hill climbing on the connection set.
#
# For a finite group G of order N and a connection set S (|S| = d, distinct),
# the Haar graph has vertices a_g, b_g (g in G) and edges a_g -- b_{g s}, s in S.
# It is d-regular and bipartite, and left multiplication by G is an automorphism,
# so the diameter is at most D iff every a-vertex and every b-vertex is reached
# within distance D from the two roots a_e and b_e. The cost of S is the number
# of vertices left unreached from those two roots, and a hill climber swaps one
# element of S at a time. Groups are cyclic Z_N or semidirect products
# Z_m x| Z_k (possibly nonabelian), evaluated with vectorised tables. Groups
# are searched round-robin, and any group that reaches cost 0 is verified by
# lib.is_valid and kept if it improves the best graph found so far.
# ----------------------------------------------------------------------------

def _group_tables(spec):
    """Multiplication and inverse tables for ('c', N) or ('s', m, k, r). Element 0 is the identity."""
    if spec[0] == 'c':
        N = spec[1]
        x = np.arange(N, dtype=np.int64)
        M = (x[:, None] + x[None, :]) % N
    else:
        _, m, k, r = spec
        N = m * k
        pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        x = np.arange(N, dtype=np.int64)
        a, b = x // k, x % k
        M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = (M == 0).argmax(axis=1)
    return N, M.astype(np.int64), inv.astype(np.int64)


def _group_specs(lo, hi, d, rng):
    """Cyclic groups plus up to two nonabelian semidirect products per order, for N in [lo, hi]."""
    specs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            break
        specs.append(('c', N))
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            nonab = [r for r in rs if r != 1]
            rng.shuffle(nonab)
            picks = nonab[:2] if nonab else rs[:1]
            for r in picks:
                specs.append(('s', m, k, r))
    return specs


def _reach(N, M, S, Sinv, root):
    """Number of vertices NOT reached from root within distance 4 in the Haar graph."""
    seen = bytearray(2 * N)
    seen[root] = 1
    frontier = [root]
    cnt = 1
    for _ in range(4):
        nxt = []
        for v in frontier:
            if v < N:
                row = M[v]
                for s in S:
                    w = N + int(row[s])
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = M[v - N]
                for si in Sinv:
                    w = int(row[si])
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * N - cnt


def _haar_cost(N, M, inv, S):
    Sinv = [int(inv[s]) for s in S]
    return _reach(N, M, S, Sinv, 0) + _reach(N, M, S, Sinv, N)


def _new_state(spec, d, rng):
    N, M, inv = _group_tables(spec)
    S = rng.sample(range(N), d)
    return {'N': N, 'M': M, 'inv': inv, 'S': S,
            'cost': _haar_cost(N, M, inv, S), 'stall': 0}


def _haar_steps(st, d, rng, iters):
    """Run up to `iters` hill-climbing moves; return True once the cost reaches 0."""
    N, M, inv = st['N'], st['M'], st['inv']
    for _ in range(iters):
        if st['cost'] == 0:
            return True
        if st['stall'] > 400:
            st['S'] = rng.sample(range(N), d)
            st['cost'] = _haar_cost(N, M, inv, st['S'])
            st['stall'] = 0
            continue
        S = st['S']
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            st['stall'] += 1
            continue
        S2 = list(S)
        S2[i] = x
        c2 = _haar_cost(N, M, inv, S2)
        if c2 <= st['cost']:
            st['stall'] = 0 if c2 < st['cost'] else st['stall'] + 1
            st['S'] = S2
            st['cost'] = c2
        else:
            st['stall'] += 1
    return st['cost'] == 0


def _haar_search(d, lo, hi, deadline, rng, best, consider):
    specs = _group_specs(lo, hi, d, rng)
    states = []
    for sp in specs:
        if time.monotonic() >= deadline:
            break
        states.append(_new_state(sp, d, rng))
    active = states
    while active and time.monotonic() < deadline:
        nxt = []
        for st in active:
            if time.monotonic() >= deadline:
                nxt.extend(active[active.index(st):])
                break
            if 2 * st['N'] <= best[0]:
                continue
            if _haar_steps(st, d, rng, 20):
                N, S, M = st['N'], st['S'], st['M']
                edges = [(g, N + int(M[g][s])) for g in range(N) for s in S]
                consider(2 * N, edges)
                continue
            nxt.append(st)
        active = nxt


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _expand_loop(bases, best, d, D, expand_deadline, rng, consider):
    rot = 0
    while bases and time.monotonic() < expand_deadline:
        if best[0] > 0 and rng.random() < 0.3:
            src = (best[0], best[1])
        else:
            src = bases[rot % len(bases)]
            rot += 1
        n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
        consider(n2, e2)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, fb_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    moore = lib._moore_bound(d, D)
    # Calibration shortcut: already at the Moore bound, nothing to gain.
    if best[0] >= moore:
        return best[0], best[1]

    bases = []
    if D == 3:
        bases = [b for b in _best_pg(d, 2)]
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= start + 0.2 * time_limit:
                break
            bases.append(_gq_w(q))

    for b in bases:
        consider(b[0], b[1])

    # Phase 1: diameter-preserving growth from the algebraic bases.
    _expand_loop(bases, best, d, D, start + 0.35 * time_limit, rng, consider)

    # Phase 2: group-Haar search, aimed at orders above the current best.
    lo = best[0] // 2 + 1
    hi = moore // 2
    if hi >= lo and time.monotonic() < start + 0.85 * time_limit:
        _haar_search(d, lo, hi, start + 0.85 * time_limit, rng, best, consider)

    return best[0], best[1]
