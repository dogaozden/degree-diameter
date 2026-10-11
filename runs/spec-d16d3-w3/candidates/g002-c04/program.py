import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane and generalized quadrangle bases.
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# From PG(2, q) incidence with spare s = d - q - 1, choose a point set S such
# that every line holds <= s points of S and every point lies on <= s lines
# indexed by S. Add an A-vertex per point of S (joined to its q+1 lines) and a
# B-vertex per line of S (joined to its q+1 points). Diameter stays 3.
# The set S is searched by an iterated plateau local search.
# ----------------------------------------------------------------------------

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


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


class _ArcState:
    """Mutable feasible-set state with per-line and per-point load counters."""

    def __init__(self, m, s, pl, lp):
        self.m = m
        self.s = s
        self.pl = pl
        self.lp = lp
        self.cl = [0] * m
        self.cp = [0] * m
        self.inS = [False] * m
        self.S = []

    def add(self, P):
        self.inS[P] = True
        self.S.append(P)
        for L in self.pl[P]:
            self.cl[L] += 1
        for Q in self.lp[P]:
            self.cp[Q] += 1

    def remove(self, P):
        self.inS[P] = False
        self.S.remove(P)
        for L in self.pl[P]:
            self.cl[L] -= 1
        for Q in self.lp[P]:
            self.cp[Q] -= 1

    def fits(self, P):
        s = self.s
        return (all(self.cl[L] < s for L in self.pl[P])
                and all(self.cp[Q] < s for Q in self.lp[P]))

    def blockers(self, P):
        s = self.s
        satL = {L for L in self.pl[P] if self.cl[L] >= s}
        satQ = {Q for Q in self.lp[P] if self.cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in self.S
                if any(L in satL for L in self.pl[R])
                or any(Q in satQ for Q in self.lp[R])]


def _greedy_fill(m, s, pl, lp, rng):
    st = _ArcState(m, s, pl, lp)
    order = list(range(m))
    rng.shuffle(order)
    for P in order:
        if st.fits(P):
            st.add(P)
    return list(st.S)


def _arc_local(m, s, pl, lp, S0, rng, deadline, max_iters):
    """Plateau local search from a feasible S0. Returns the largest feasible set seen."""
    st = _ArcState(m, s, pl, lp)
    for P in S0:
        st.add(P)
    best = list(st.S)
    for it in range(1, max_iters + 1):
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if st.inS[P]:
            continue
        if st.fits(P):
            st.add(P)
            if len(st.S) > len(best):
                best = list(st.S)
            continue
        B = st.blockers(P)
        if not B:
            continue
        if rng.random() < 0.99 or len(B) > 4:
            # Plateau swap: drop one blocker, insert P if it now fits.
            R = rng.choice(B)
            st.remove(R)
            if st.fits(P):
                st.add(P)
            else:
                st.add(R)
        else:
            # Rare perturbation: drop all blockers, insert P if it fits.
            for R in B:
                st.remove(R)
            if st.fits(P):
                st.add(P)
            else:
                for R in B:
                    st.add(R)
    return best


def _arc_ils(m, s, pl, lp, rng, deadline):
    """Iterated local search: restarts from the current round's best with small perturbations."""
    gbest = []
    cur = None
    while time.monotonic() < deadline:
        if cur is None or rng.random() < 0.2:
            start = _greedy_fill(m, s, pl, lp, rng)
        else:
            start = list(cur)
            for _ in range(min(len(start), rng.randint(1, 4))):
                start.pop(rng.randrange(len(start)))
        cur = _arc_local(m, s, pl, lp, start, rng, deadline, 12000)
        if len(cur) > len(gbest):
            gbest = list(cur)
    return gbest


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """Arc-extended graphs for the most promising prime powers q (by counting bound)."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        bound = 2 * m + 2 * (s * m // (q + 1))
        qs.append((bound, q, s))
    if not qs:
        return []
    qs.sort(reverse=True)
    top_bound = qs[0][0]
    chosen = [t for t in qs if t[0] > 0.9 * top_bound][:3]

    out = []
    for idx, (bound, q, s) in enumerate(chosen):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(chosen) - idx)
        m, edges, pl, lp, index, pts = _pg_data(q)
        S = _arc_ils(m, s, pl, lp, rng, now + share)
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


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
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


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
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Pairs (representative, vertex) not within distance D. Zero means valid.

    Returns early with a value above `limit` once the running total exceeds it.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Annealing over voltages and B-assignments.

    A move with new cost c2 is accepted iff c2 <= cost - T*ln(u), u ~ U(0,1].
    This is Metropolis acceptance and doubles as the early-exit limit.
    Temperature decays geometrically from T0 (scaled to the initial cost) to 0.05.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    ratio = (0.05 / T0) ** (1.0 / max(1, iters)) if T0 > 0.05 else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T *= ratio
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def done():
        # Already at the Moore bound: nothing can beat it.
        return best_n >= lib.moore_bound(d, D)

    if D >= 3 and not done():
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if not done():
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.08 * time_limit, rng)
                consider(n2, e2)

    if D == 3 and not done():
        arc_deadline = min(deadline, start + 0.68 * time_limit)
        arcs = _arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda c: -c[0])
        for n_c, e_c in arcs:
            consider(n_c, e_c)
        if arcs and not done():
            n_b, e_b = arcs[0]
            n3, e3 = _grow(n_b, e_b, d, D, min(deadline, start + 0.78 * time_limit),
                           random.Random(seed * 104729 + d))
            consider(n3, e3)

    if D >= 4 and not done():
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, min(deadline, start + 0.4 * time_limit), rng)
            consider(n2, e2)

    # Remaining time: annealed group voltage lifts, with occasional Haar attempts for small D.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline and not done():
        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=600)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
