import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc family (D = 3). For d = q + 1 + s, take PG(2, q) and a
# set S of points with at most s points of S on every line and at most s lines
# through each point of S. Add one A-vertex per point of S (joined to the q+1
# lines through it) and one B-vertex per line of S (joined to its q+1 points).
# A conic (an arc) gives q+1 extra pairs; for d = 16 this is order 394.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, S):
    """Incidence graph of PG(2,q) plus an A-vertex and a B-vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in pl[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build an arc-extended PG(2, q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp = _pg(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [_greedy_arc(m, s, pl, lp, rng, 20, deadline)]
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, pl, lp, S)
        out.append((n, E))
    return out


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover-based vertex addition and edge saturation.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Greedy cover of `full` by at most d candidate neighbourhoods; None if it fails."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within distance D-1."""
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
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
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
    """Join deficient opposite-side vertices greedily in random order."""
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
# Haar-type bi-Cayley graphs over a group G of order m with a k-set S:
# A_g ~ B_{g s} for s in S. Diameter <= 3 iff S S^{-1} = G and S^{-1} S = G
# (a "difference cover"). The order is 2m with degree k. For k = 16 the
# ceiling is m <= k(k-1)+1 = 241, so orders above 394 need m >= 198.
# Cyclic and small semidirect groups Z_a x| Z_b are searched by annealing.
# ----------------------------------------------------------------------------

def _group_pool(n, rng):
    """Group descriptors of order n: the cyclic group plus some semidirect products."""
    pool = [("cyc", n)]
    for k2 in range(2, n):
        if n % k2:
            continue
        m1 = n // k2
        if m1 < 2:
            continue
        rs = [r for r in range(2, m1)
              if math.gcd(r, m1) == 1 and pow(r, k2, m1) == 1 % m1]
        rng.shuffle(rs)
        pool += [("sd", m1, k2, r) for r in rs[:3]]
    rng.shuffle(pool)
    return pool


def _tables(desc):
    """Multiplication, inverse and difference tables for a group descriptor."""
    if desc[0] == "cyc":
        n, mul, inv = lib.cyclic_group(desc[1])
        sym = True
    else:
        n, mul, inv = lib.semidirect_group(desc[1], desc[2], desc[3])
        sym = False
    M = [[mul(x, y) for y in range(n)] for x in range(n)]
    I = [inv(x) for x in range(n)]
    A = [[M[s][I[t]] for t in range(n)] for s in range(n)]
    B = None if sym else [[M[I[s]][t] for t in range(n)] for s in range(n)]
    return n, M, A, B, sym


def _cover_anneal(n, A, B, sym, k, rng, deadline):
    """Find a k-subset S of a group of order n with S S^-1 and S^-1 S covering all non-identity elements."""
    S = rng.sample(range(n), k)
    inS = [False] * n
    for s in S:
        inS[s] = True
    cA = [0] * n
    cB = [0] * n
    for x in S:
        for y in S:
            if x != y:
                cA[A[x][y]] += 1
                if not sym:
                    cB[B[x][y]] += 1
    unc = sum(1 for g in range(1, n) if cA[g] == 0)
    if not sym:
        unc += sum(1 for g in range(1, n) if cB[g] == 0)
    if unc == 0:
        return S
    period = 100000
    it = 0
    while True:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        ph = it % period
        T = 0.8 * (0.02 ** (ph / period))
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(n)
        if inS[y]:
            continue
        others = S[:i] + S[i + 1:]
        change = 0
        # Remove x: decrement its difference counts.
        for s in others:
            g = A[x][s]
            c = cA[g] - 1
            cA[g] = c
            if c == 0:
                change += 1
            g = A[s][x]
            c = cA[g] - 1
            cA[g] = c
            if c == 0:
                change += 1
            if not sym:
                g = B[x][s]
                c = cB[g] - 1
                cB[g] = c
                if c == 0:
                    change += 1
                g = B[s][x]
                c = cB[g] - 1
                cB[g] = c
                if c == 0:
                    change += 1
        # Add y: increment its difference counts.
        for s in others:
            g = A[y][s]
            if cA[g] == 0:
                change -= 1
            cA[g] += 1
            g = A[s][y]
            if cA[g] == 0:
                change -= 1
            cA[g] += 1
            if not sym:
                g = B[y][s]
                if cB[g] == 0:
                    change -= 1
                cB[g] += 1
                g = B[s][y]
                if cB[g] == 0:
                    change -= 1
                cB[g] += 1
        if change <= 0 or rng.random() < math.exp(-change / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
            unc += change
            if unc == 0:
                return S
        else:
            # Revert: remove y, restore x.
            for s in others:
                cA[A[y][s]] -= 1
                cA[A[s][y]] -= 1
                if not sym:
                    cB[B[y][s]] -= 1
                    cB[B[s][y]] -= 1
            for s in others:
                cA[A[x][s]] += 1
                cA[A[s][x]] += 1
                if not sym:
                    cB[B[x][s]] += 1
                    cB[B[s][x]] += 1


def _find_cover(n, k, rng, deadline, slice_len):
    """Search over group descriptors of order n until a cover is found or the deadline passes."""
    pool = _group_pool(n, rng)
    cache = {}
    i = 0
    while time.monotonic() < deadline:
        desc = pool[i % len(pool)]
        i += 1
        if desc not in cache:
            cache[desc] = _tables(desc)
        order, M, A, B, sym = cache[desc]
        end = min(deadline, time.monotonic() + slice_len)
        S = _cover_anneal(order, A, B, sym, k, rng, end)
        if S is not None:
            return M, S
    return None


def _group_edges(n, M, S):
    """Bi-Cayley graph: A_g = g, B_h = n + h, edges A_g ~ B_{g s} for s in S."""
    E = []
    for g in range(n):
        row = M[g]
        for s in S:
            E.append((g, n + row[s]))
    return 2 * n, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 50.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 2:
        return best_n, list(best_E)

    if D == 3:
        # Arc-extended projective planes (order 394 at d = 16), grown by cover extension.
        arcs = _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d))
        for n_a, E_a in arcs:
            consider(n_a, E_a)
        if arcs:
            arcs.sort(key=lambda t: -t[0])
            n_a, E_a = arcs[0]
            n2, E2 = _grow(n_a, E_a, d, D, time.monotonic() + 0.08 * budget, rng)
            consider(n2, E2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Difference-cover search: order 2m with m > best_n / 2, climbing m upward.
    k = d
    mmax = k * (k - 1) + 1
    m = max(k, best_n // 2 + 1)
    slice_len = max(1.0, min(5.0, 0.1 * budget))
    while m <= mmax and time.monotonic() < deadline:
        res = _find_cover(m, k, rng, deadline, slice_len)
        if res is None:
            break
        M, S = res
        n2, E2 = _group_edges(m, M, S)
        consider(n2, E2)
        m += 1

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
