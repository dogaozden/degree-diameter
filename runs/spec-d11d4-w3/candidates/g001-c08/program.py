import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------
# Radius-3 balls and greedy set-cover extension for diameter 4.
# ----------------------------------------------------------------------------

def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _greedy_cover(s0, spare, reach, color, full, d, rng):
    """Try to cover all vertices with R3 balls of same-colour spare vertices starting at s0; return S or None."""
    pool = [v for v in spare if color[v] == color[s0] and v != s0]
    S = [s0]
    unc = full & ~reach[s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best == 0:
            return None
        tied = [pool[i] for i, g in enumerate(gains) if g == best]
        bv = rng.choice(tied)
        S.append(bv)
        unc &= ~reach[bv]
        pool.remove(bv)
    if unc:
        return None
    return S


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)

    fails = 0
    while time.monotonic() < deadline and fails < 400:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        cover = None
        for _ in range(12):
            if time.monotonic() >= deadline:
                break
            s0 = rng.choice(spare)
            cover = _greedy_cover(s0, spare, reach, color, full, d, rng)
            if cover is not None:
                break
        if cover is None:
            fails += 1
            continue
        x = n
        n += 1
        for s in cover:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(cover))
        color.append(1 - color[cover[0]])
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------
# NEW: bipartite group lifts with a single base edge-set, found by local search.
#
# Graph: vertices a_x and b_y (x, y in G), a_x ~ b_{x*s} for s in S, |S| = d.
# This is a Haar-type lift over a finite group G; left multiplication is an
# automorphism, so diameter <= 4 holds iff every vertex is within distance 4
# of a_e and of b_e (e = identity, index 0 in lib's group encodings).
# Search minimises the number of unreached pairs by swapping elements of S.
# ----------------------------------------------------------------------------

def _reach(N, fw, bw, from_a):
    """Count vertices within 4 steps of a_e (from_a) or b_e (not from_a)."""
    seenA = bytearray(N)
    seenB = bytearray(N)
    (seenA if from_a else seenB)[0] = 1
    front = [0]
    use_fwd = from_a
    for _ in range(4):
        nxt = []
        if use_fwd:
            for col in fw:
                for x in front:
                    y = col[x]
                    if not seenB[y]:
                        seenB[y] = 1
                        nxt.append(y)
        else:
            for col in bw:
                for y in front:
                    x = col[y]
                    if not seenA[x]:
                        seenA[x] = 1
                        nxt.append(x)
        front = nxt
        use_fwd = not use_fwd
    return sum(seenA) + sum(seenB)


def _groups_of_order(N, rng, max_semi=3):
    """Return a list of (order, mul, inv) groups of order N: cyclic plus a few semidirect products."""
    out = [lib.cyclic_group(N)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:max_semi]:
            try:
                out.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return out


def _hill(N, grp, d, D, deadline, rng, consider):
    """Local search over d-subsets S of the group; on success, offer the lift to consider()."""
    if N < d + 1:
        return False
    _, mul, inv = grp
    cache = {}

    def cols(s):
        c = cache.get(s)
        if c is None:
            if len(cache) > 400:
                cache.clear()
            si = inv(s)
            c = ([mul(x, s) for x in range(N)], [mul(y, si) for y in range(N)])
            cache[s] = c
        return c

    def score(S):
        cs = [cols(s) for s in S]
        fw = [c[0] for c in cs]
        bw = [c[1] for c in cs]
        return (2 * N - _reach(N, fw, bw, True)) + (2 * N - _reach(N, fw, bw, False))

    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        cur = score(S)
        stall = 0
        while cur > 0 and stall < 400 and time.monotonic() < deadline:
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                stall += 1
                continue
            T = list(S)
            T[i] = x
            sc = score(T)
            if sc <= cur:
                stall = 0 if sc < cur else stall + 1
                S, cur = T, sc
            else:
                stall += 1
        if cur == 0:
            n, edges = lib.group_lift(2, [(0, 1, s) for s in S], N, mul)
            consider(n, edges)
            return True
    return False


def _lift_stage(d, D, deadline, rng, consider, best_n):
    """Repeatedly pick group orders just above the current record half and search for lifts."""
    while time.monotonic() < deadline - 0.5:
        lo = best_n() // 2 + 1
        N = lo + rng.randrange(0, 12)
        groups = _groups_of_order(N, rng)
        rng.shuffle(groups)
        before = best_n()
        for grp in groups[:4]:
            if time.monotonic() >= deadline:
                break
            slice_end = min(deadline, time.monotonic() + 6.0)
            _hill(N, grp, d, D, slice_end, rng, consider)
            if best_n() > before:
                break


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.25 * budget
            ext_deadline = t0 + 0.4 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, ext_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if D == 4 and d >= 5:
        try:
            _lift_stage(d, D, deadline, rng, consider, lambda: best[0])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
