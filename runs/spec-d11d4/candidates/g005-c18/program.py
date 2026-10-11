import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW: rotation-bitset defect for cyclic 2-vertex lifts.
#
# Base: two vertices a, b joined by d darts with voltages T (a subset of Z_N),
# so a_x ~ b_{x+t} for t in T. A set of a-indices (or b-indices) is an N-bit
# integer, and translating it by t is a cyclic rotation. One BFS layer therefore
# costs d rotations on bigints. Translation by Z_N is an automorphism that is
# transitive on each side, so only BFS from a_0 and from b_0 has to be checked.
# T[0] is fixed to 0 because relabelling b shifts every voltage by a constant.
# A simulated-annealing search over the other d-1 voltages uses this as the cost.
# ----------------------------------------------------------------------------

def _eval_rot(T, N, D, mask):
    """Number of (source, vertex) pairs at distance > D from a_0 and from b_0."""
    fw = [(t, N - t) for t in T]                              # A -> B: rotate by t
    bw = [(k, N - k) for k in ((N - t) % N for t in T)]       # B -> A: rotate by -t
    total = 0
    for s in (0, 1):
        seen = [0, 0]
        seen[s] = 1
        front = 1
        side = s
        reached = 1
        for _ in range(D):
            nf = 0
            for k, nk in (fw if side == 0 else bw):
                nf |= (front << k) | (front >> nk)
            nf &= mask
            side ^= 1
            nf &= ~seen[side]
            if not nf:
                break
            seen[side] |= nf
            reached += nf.bit_count()
            front = nf
        total += 2 * N - reached
    return total


def _anneal_rot(N, d, D, rng, deadline):
    """Search for d voltages in Z_N (with 0 included) whose lift has diameter <= D."""
    mask = (1 << N) - 1
    if d == 1:
        T = [0]
        return T if _eval_rot(T, N, D, mask) == 0 else None
    while time.monotonic() < deadline:
        T = [0] + rng.sample(range(1, N), d - 1)
        cur = _eval_rot(T, N, D, mask)
        iters = 6000
        for it in range(iters):
            if cur == 0:
                return T
            if (it & 127) == 0 and time.monotonic() >= deadline:
                return None
            temp = 3.0 * (0.03 / 3.0) ** (it / iters)
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in T:
                continue
            new = T[:]
            new[i] = c
            val = _eval_rot(new, N, D, mask)
            delta = val - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                T, cur = new, val
        if cur == 0:
            return T
    return None


def _lift_search(d, D, deadline, rng):
    """Coarse descent over orders N from the Moore-type ceiling, then fine upward scan."""
    hi = lib._moore_bound(d, D) // 2
    if hi < d:
        return None
    coarse = max(1, hi // 40)
    N = hi
    found = None
    while N >= d and time.monotonic() < deadline:
        T = _anneal_rot(N, d, D, rng, min(deadline, time.monotonic() + 0.5))
        if T is not None:
            found = (N, T)
            break
        N -= coarse
    if found is None:
        return None
    best = found
    N = found[0] + 1
    fails = 0
    while fails < 2 and time.monotonic() < deadline:
        T = _anneal_rot(N, d, D, rng, min(deadline, time.monotonic() + 1.5))
        if T is not None:
            best = (N, T)
            fails = 0
        else:
            fails += 1
        N += 1
    return best


# ----------------------------------------------------------------------------
# Parent constructions (kept as a safe fallback):
# PG(2,q) for D = 3, and the generalized quadrangle W(q) for D = 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of W(q): bipartite, diameter 4, degree q+1."""
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
            thr = max(1, best_g - 1)
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _cover_ls(cands, ball, full, d, rng, steps, deadline):
    if not cands:
        return None
    k = min(d, len(cands))
    S = rng.sample(cands, k)
    in_s = set(S)

    def union(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~union(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            break
        if (step & 255) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~union(rest)
        best_t, best_g = None, -1
        for t in rng.sample(cands, min(40, len(cands))):
            if t in in_s:
                continue
            g = (ball[t] & miss).bit_count()
            if g > best_g:
                best_t, best_g = t, g
        if best_t is None:
            continue
        newcost = (miss & ~ball[best_t]).bit_count()
        if newcost <= cost or rng.random() < 0.02:
            in_s.discard(S[i])
            S[i] = best_t
            in_s.add(best_t)
            cost = newcost
    return S if cost == 0 else None


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(20):
                if time.monotonic() >= deadline:
                    break
                if attempt < 4:
                    chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 1500, deadline)
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
    """Join spare-degree vertices on opposite sides in random order (keeps bipartiteness)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Driver. Every candidate is validated with lib.is_valid before it can be kept.
# The fallback K_{d,d} is always valid for D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.45 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        # New path: rotation-bitset annealing over cyclic 2-vertex lifts.
        res = _lift_search(d, D, start + 0.55 * time_limit, rng)
        if res is not None:
            n_, e_ = lib.haar_graph(res[0], res[1])
            consider(n_, e_)

        # Safe fallback: GQ base with randomized cover growth for the rest of the budget.
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            t = 0
            grow_deadline = start + 0.75 * time_limit
            while time.monotonic() < grow_deadline and t < 12:
                n2, e2 = _grow(gq[0], gq[1], d, D, grow_deadline,
                               random.Random(seed * 131 + t))
                consider(n2, e2)
                t += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
