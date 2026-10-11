import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined D = 3 search.
#
# (1) Arc-extended projective plane graphs. Start from the incidence graph of
#     PG(2, q) (points 0..m-1, lines m..2m-1). Choose SA (points) so that every
#     line holds <= s points of SA, and SB (lines) so that every point lies on
#     <= s lines of SB, with s = d - q - 1. Add one new A-vertex per SA point
#     (joined to its q+1 lines) and one new B-vertex per SB line (joined to its
#     q+1 points). The two sides are independent. SA and SB are optimized by
#     iterated local search (plateau moves plus perturbation restarts), which
#     can go beyond the conic seed.
# (2) Cyclic Haar graphs H(m, S) from difference covers of size d (diameter 3).
# (3) Greedy vertex insertion with ball-cover certificates on the best graph.
#
# For D >= 4: GQ(q) incidence graphs, voltage-lift annealing, and the arc graphs.
# ----------------------------------------------------------------------------

_ILS_PER_M = 1500      # iteration cap per unit of m for the arc local search
_LS_STALL = 4000       # accepted non-improving moves before a perturbation restart


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


class _ArcState:
    """A set S of elements; element x hits targets nbr[x]; each target may be hit <= s times."""

    def __init__(self, m, s, nbr):
        self.m = m
        self.s = s
        self.nbr = nbr
        self.inS = [False] * m
        self.hits = [set() for _ in range(m)]
        self.members = set()

    def add(self, x):
        self.inS[x] = True
        self.members.add(x)
        for t in self.nbr[x]:
            self.hits[t].add(x)

    def remove(self, y):
        self.inS[y] = False
        self.members.discard(y)
        for t in self.nbr[y]:
            self.hits[t].discard(y)

    def fits(self, x):
        return all(len(self.hits[t]) < self.s for t in self.nbr[x])

    def greedy(self, rng):
        order = list(range(self.m))
        rng.shuffle(order)
        for x in order:
            if not self.inS[x] and self.fits(x):
                self.add(x)

    def reset(self, S):
        for y in list(self.members):
            self.remove(y)
        for x in S:
            self.add(x)


def _ils(m, s, nbr, S0, rng, deadline, iters):
    """Iterated local search for a large set with every target hit by <= s elements.

    A move inserts a random outside element x and removes the blockers of x
    (one per saturated target). Removing 0 members improves the set, 1 is a
    plateau move, 2 is accepted rarely. After many non-improving moves the
    search restarts from the best set with 3 random members dropped.
    """
    st = _ArcState(m, s, nbr)
    for x in S0:
        st.add(x)
    st.greedy(rng)
    best = sorted(st.members)
    if s < 1:
        return best
    best_size = len(best)
    stall = 0
    for it in range(iters):
        if (it & 511) == 0 and time.monotonic() > deadline:
            break
        if stall > _LS_STALL:
            st.reset(best)
            for y in rng.sample(best, min(3, len(best))):
                st.remove(y)
            st.greedy(rng)
            stall = 0
        x = rng.randrange(m)
        if st.inS[x]:
            continue
        rem = []
        ok = True
        for t in nbr[x]:
            cur = [y for y in st.hits[t] if y not in rem]
            if len(cur) >= s:
                rem.append(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            st.remove(y)
        st.add(x)
        size = len(st.members)
        if size > best_size:
            best = sorted(st.members)
            best_size = size
            stall = 0
        else:
            stall += 1
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d.

    Planes are processed in increasing q; each gets an equal share of the
    remaining time, so the largest plane (which matters most) gets the rest.
    """
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        end = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA0 = _greedy_side(m, s, point_lines, rng, 20, end)
        SB0 = _greedy_side(m, s, line_points, rng, 20, end)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA0) and _loads_ok(cs, s, m, point_lines):
                SA0 = cs
            if len(cs) > len(SB0) and _loads_ok(cs, s, m, line_points):
                SB0 = cs

        iters = _ILS_PER_M * m
        mid = time.monotonic() + (end - time.monotonic()) / 2
        SA = _ils(m, s, point_lines, SA0, rng, mid, iters)
        SB = _ils(m, s, line_points, SB0, rng, end, iters)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Cyclic Haar graphs from difference covers (diameter 3).
#
# S a k-subset of Z_m with every nonzero residue a difference s - t. Then
# H(m, S) (a_i ~ b_{i+s}) is k-regular with diameter 3.
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    """Replace S[i] by y (y not in S), updating cnt and the zero count. Returns the new zero count."""
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            a = (old - t) % m
            b = (t - old) % m
            cnt[a] -= 1
            if cnt[a] == 0:
                zeros += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            a = (y - t) % m
            b = (t - y) % m
            if cnt[a] == 0:
                zeros -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                zeros -= 1
            cnt[b] += 1
    return zeros


def _cover_search(k, m, deadline, rng):
    """Find a k-subset S of Z_m whose nonzero differences cover Z_m \\ {0}; return sorted S or None."""
    if k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    cnt, zeros = _diff_counts(S, m)
    T = 0.3
    moves = 0
    while zeros > 0:
        moves += 1
        if moves % 512 == 0 and time.monotonic() > deadline:
            return None
        if moves % 200000 == 0:
            S = rng.sample(range(m), k)
            cnt, zeros = _diff_counts(S, m)
            continue
        i = rng.randrange(k)
        y = rng.randrange(m)
        if y in S:
            continue
        old = S[i]
        z = _move(S, cnt, i, y, m, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _move(S, cnt, i, old, m, z)
    return sorted(S)


def _difference_graph(d, deadline, rng):
    """Largest cyclic Haar graph H(m, S) with |S| = d found before the deadline, as (n, edges), or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        S = _cover_search(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates.
#
# A new vertex w joined to N (opposite colour) reaches x within D iff x lies
# within distance D-1 of some u in N. Adding vertices/edges never breaks
# diameter <= D, and every candidate is re-checked by lib.is_valid anyway.
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
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


def _ball_masks(n, adj, R):
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(3):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 2 fallback).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Arc-extended plane graphs (diameter 3), optimized independently on each side.
        arcs = _arc_extensions(d, start + 0.68 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs:
            consider(n_c, e_c)
        # Cyclic Haar graph from a difference cover of size d (diameter 3).
        hg = _difference_graph(d, start + 0.80 * time_limit, rng)
        if hg is not None:
            consider(hg[0], hg[1])
    else:
        if D >= 3:
            arcs = _arc_extensions(d, start + 0.35 * time_limit, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs:
                consider(n_c, e_c)
        if D >= 4 and time.monotonic() < start + 0.45 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        search_end = start + 0.75 * time_limit
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Final greedy insertion on the best graph found so far.
    if D >= 2 and time.monotonic() < start + 0.92 * time_limit:
        n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.92 * time_limit)
        consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
