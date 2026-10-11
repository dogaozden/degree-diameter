import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
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


def _colors(n, adj):
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


def _balls(n, adj, r):
    """Bitmask of the radius-r ball around every vertex."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return ball


def _ball_matrix(n, ball):
    """0/1 int32 matrix B with B[v, w] = 1 iff w lies in the ball of v."""
    B = np.zeros((n, n), dtype=np.int32)
    for v in range(n):
        s = format(ball[v], "b").zfill(n)[::-1]
        B[v] = np.frombuffer(s.encode(), dtype=np.uint8) - 48
    return B


def _saturate(n, edges, d, rng):
    """Add random edges between opposite-side vertices with spare degree (never hurts distances)."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _colors(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


def _remove_vertex(n, edges, x):
    """Delete vertex x; the last vertex takes its label. Returns (n-1, edges)."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


# ----------------------------------------------------------------------------
# NEW: annealed dominating-set search for vertex insertion.
#
# A new vertex v on one side is diameter-safe if its neighbours s satisfy
# "every vertex lies within distance D-1 of some neighbour". This is a
# bounded-size set cover over radius-(D-1) balls. Greedy cover often stalls
# at the degree cap, so we anneal over swaps of a fixed-size chosen set,
# with coverage counts kept in a numpy vector for cheap swap evaluation.
# ----------------------------------------------------------------------------

def _cover_search(A, d, rng, iters, deadline):
    """Pick min(d, m) rows of 0/1 matrix A so every column is hit. Returns row indices or None."""
    m, n = A.shape
    if m == 0:
        return None
    k = min(d, m)
    cnt = np.zeros(n, dtype=np.int32)
    S = []
    noise = np.array([rng.random() for _ in range(m)]) * 0.9
    for _ in range(k):
        gain = A @ (cnt == 0).astype(np.int32)
        score = gain + noise
        for i in S:
            score[i] = -1e9
        i = int(np.argmax(score))
        S.append(i)
        cnt += A[i]
    unc = int(np.count_nonzero(cnt == 0))
    inS = np.zeros(m, dtype=bool)
    inS[S] = True

    for it in range(iters):
        if unc == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T = 0.7 * (0.02 ** (it / iters))
        p = rng.randrange(k)
        j = rng.randrange(m)
        if inS[j]:
            continue
        old = S[p]
        new_cnt = cnt - A[old] + A[j]
        new_unc = int(np.count_nonzero(new_cnt == 0))
        delta = new_unc - unc
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cnt = new_cnt
            inS[old] = False
            inS[j] = True
            S[p] = j
            unc = new_unc
    return list(S) if unc == 0 else None


def _grow(n, edges, d, D, deadline, rng, fails_allowed=4):
    """Repeatedly insert cover-attached vertices (via annealed cover search), saturating after each."""
    cur_n, cur_e = n, list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < fails_allowed:
        adj = _adjacency(cur_n, cur_e)
        deg = [len(a) for a in adj]
        color = _colors(cur_n, adj)
        if any(c < 0 for c in color):
            break
        B = _ball_matrix(cur_n, _balls(cur_n, adj, D - 1))
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for c in sides:
            cands = [s for s in range(cur_n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            S = _cover_search(B[cands], d, rng, 1200, deadline)
            if S is None:
                continue
            v = cur_n
            cur_e.extend((cands[i], v) for i in S)
            cur_n += 1
            added = True
            break
        if added:
            cur_e = _saturate(cur_n, cur_e, d, rng)
            fails = 0
        else:
            fails += 1
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing (kept from the parent).
# Twinning v gives v' with the same neighbourhood; diameter and bipartiteness
# are preserved when every neighbour of v has a spare slot.
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
    color = _colors(n, adj)
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


def _expand(n, edges, d, D, deadline, rng, rounds=4):
    """Alternate twin packing on both sides with cover growth, while the graph keeps growing."""
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Perturb-and-regrow search: delete a random vertex, repair the diameter with
# saturation edges, then regrow with annealed cover insertions. Equal-size
# moves are accepted so the search can drift across plateaus.
# ----------------------------------------------------------------------------

def _perturb(best, d, D, deadline, rng):
    cur_n, cur_e = best
    best_n, best_e = best
    while time.monotonic() < deadline:
        x = rng.randrange(cur_n)
        rn, re = _remove_vertex(cur_n, cur_e, x)
        if rn < 2:
            continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                continue
        rn, re = _grow(rn, re, d, D, deadline, rng, fails_allowed=3)
        if rn >= cur_n:
            cur_n, cur_e = rn, re
            if rn > best_n and lib.is_valid(rn, re, d, D):
                best_n, best_e = rn, re
    return best_n, best_e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= lib.moore_bound(d, D):
        return best

    bases = []
    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            bases.append(pg)
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() > start + 0.15 * budget:
                break
            bases.append(_gq_w(q))
    for b in bases:
        consider(b[0], b[1])

    # Phase 1: twin packing and annealed cover growth from each base graph.
    expand_end = start + 0.35 * budget
    srcs = bases if bases else [best]
    slice_len = (expand_end - time.monotonic()) / max(1, len(srcs))
    for src in srcs:
        if time.monotonic() >= expand_end:
            break
        sub_deadline = min(expand_end, time.monotonic() + slice_len)
        n2, e2 = _expand(src[0], src[1], d, D, sub_deadline, rng)
        consider(n2, e2)

    # Phase 2: direct growth from the best graph found so far.
    if best[0] >= 2 and time.monotonic() < deadline:
        grow_end = min(deadline, time.monotonic() + 0.15 * budget)
        n2, e2 = _grow(best[0], best[1], d, D, grow_end, rng)
        consider(n2, e2)

    # Phase 3: perturb-and-regrow until the deadline.
    if best[0] >= 2 and time.monotonic() < deadline:
        pn, pe = _perturb(best, d, D, deadline, rng)
        consider(pn, pe)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
