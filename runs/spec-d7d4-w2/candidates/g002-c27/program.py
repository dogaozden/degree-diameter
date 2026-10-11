import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Basic graph helpers.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _balls(n, adj, r):
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
    return sum(n - b.bit_count() for b in _balls(n, adj, D)) // 2


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
# Twin blow-up: twin v gets the same neighbourhood, so diameter and bipartiteness
# are kept when every neighbour of v has a spare slot. Packing chooses many twins.
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
    """Choose candidates so each resource u is used by at most cap[u] chosen candidates."""
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
    adj = _adj(n, edges)
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
# Cover-based vertex extension (diameter-preserving) and edge saturation.
# A new vertex joined to a set S keeps the diameter bound iff the balls of
# radius D-1 around S cover all existing vertices.
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


def _extend_cover(n, edges, d, D, deadline, rng, restarts):
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        N = len(adj)
        full = (1 << N) - 1
        ball = _balls(N, adj, D - 1)
        added = False
        for c in (0, 1):
            cands = [s for s in range(N) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for att in range(restarts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
                if chosen:
                    break
            if chosen:
                v = N
                adj.append([])
                deg.append(0)
                color.append(1 - c)
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
    return len(adj), edges


def _saturate_edges(n, edges, d, rng):
    """Add random edges between non-adjacent opposite-side vertices with spare degree.
    Adding edges never increases distances, so the diameter bound is preserved."""
    edges = list(edges)
    adj = _adj(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, restarts=100):
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, restarts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    """Alternate twin packing on both sides with cover growth while the graph grows."""
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
# Drop-and-refill local search. Remove the vertex whose deletion leaves the
# fewest bad pairs (sampled), saturate spare slots, then regrow with covers.
# The caller validates the result before accepting it.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    def mp(v):
        return v if v < x else v - 1
    e2 = [(mp(u), mp(v)) for u, v in edges if u != x and v != x]
    return n - 1, e2


def _drop_refill(n, edges, d, D, rng, deadline, tries=12):
    best = None
    for _ in range(tries):
        if time.monotonic() >= deadline:
            break
        x = rng.randrange(n)
        n2, e2 = _remove_vertex(n, edges, x)
        b = _bad(n2, _adj(n2, e2), D)
        if best is None or b < best[0]:
            best = (b, n2, e2)
    if best is None:
        return None
    _, n2, e2 = best
    e2 = _saturate_edges(n2, e2, d, rng)
    return _grow(n2, e2, d, D, deadline, rng, 60)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.8 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # ---- Structured bases ----------------------------------------------------
    bases = []
    try:
        if D == 3:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    bases.append(lib.projective_plane_incidence(q))
                    break
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                bases.append(lib.araujo_lopez_graph(d - 2))
        elif D >= 4:
            qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
            for q in qs:
                bases.append(_gq_w(q))
    except Exception:
        pass

    for b in bases:
        consider(b[0], b[1])

    # Already at the Moore bound: nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best

    # ---- Expansion from bases and the current best ---------------------------
    expand_deadline = start + 0.35 * T
    rot = 0
    for _ in range(8):
        if not bases or time.monotonic() >= expand_deadline:
            break
        if rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        try:
            n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
            consider(n2, e2)
        except Exception:
            pass

    # ---- Main search: drop-refill, twin-grow and grow, with plateau drift ----
    cur_n, cur_e = best
    while time.monotonic() < deadline and best_n < lib.moore_bound(d, D):
        try:
            if rng.random() < 0.03:
                cur_n, cur_e = best
            r = rng.random()
            if r < 0.55:
                res = _drop_refill(cur_n, cur_e, d, D, rng, deadline)
            elif r < 0.8:
                side = rng.choice((0, 1))
                tn, te = _twin_pass(cur_n, cur_e, d, side, rng, deadline, 2000)
                res = _grow(tn, te, d, D, deadline, rng, 100)
            else:
                res = _grow(cur_n, cur_e, d, D, deadline, rng, 100)
            if res is None:
                continue
            n2, e2 = res
            if n2 >= cur_n and lib.is_valid(n2, e2, d, D):
                cur_n, cur_e = n2, e2
                if n2 > best_n:
                    best = (n2, e2)
                    best_n = n2
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
