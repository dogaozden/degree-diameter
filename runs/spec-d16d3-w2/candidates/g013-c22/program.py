import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane helpers (D = 3 arc-extended graphs)
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _arc_graph(m, edges, S, pl, lp):
    """PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P. Order 2m + 2|S|."""
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
    """For each prime power q with q + 1 <= d, build the arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, S, pl, lp)
        out.append((n, E, m, pl, lp))
    return out


# ----------------------------------------------------------------------------
# Validity-checked local search on an arc graph (D = 3).
# Moves: add a vertex adjacent to a star with spare degree, or remove a vertex.
# Every stored graph passes lib.is_valid.
# ----------------------------------------------------------------------------

def _local_search(n0, E0, m, pl, lp, d, D, deadline, rng):
    adj = {}

    def link(u, v):
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)

    def unlink_vertex(v):
        nb = adj.pop(v, set())
        for u in nb:
            s = adj[u]
            s.discard(v)
            if not s:
                del adj[u]
        return nb

    def raw():
        return [(u, v) for u in adj for v in adj[u] if u < v]

    def valid():
        n, E = lib.relabel(raw())
        return lib.is_valid(n, E, d, D)

    def load(E):
        adj.clear()
        for u, v in E:
            link(u, v)

    best_E = list(E0)
    load(E0)
    cur = len(adj)
    best_cnt = cur
    nxt = n0
    T = 0.7
    stale = 0

    while time.monotonic() < deadline:
        stale += 1
        if stale > 4000:
            load(best_E)
            cur = len(adj)
            nxt = max(max(e) for e in best_E) + 1 if best_E else n0
            stale = 0
            continue

        if rng.random() < 0.4:
            if rng.random() < 0.5:
                cand = [m + L for L in pl[rng.randrange(m)]]
            else:
                cand = list(lp[rng.randrange(m)])
            nb = [u for u in cand if len(adj.get(u, ())) < d]
            if len(nb) < 2:
                continue
            x = nxt
            nxt += 1
            for u in nb:
                link(x, u)
            kind, vid, saved = 'add', x, nb
        else:
            if not adj:
                continue
            v = rng.choice(list(adj))
            nb = unlink_vertex(v)
            kind, vid, saved = 'rem', v, nb

        def undo():
            if kind == 'add':
                unlink_vertex(vid)
            else:
                adj[vid] = set()
                for u in saved:
                    link(vid, u)

        delta = len(adj) - cur
        if delta < 0 and rng.random() >= math.exp(delta / T):
            undo()
            continue
        if not valid():
            undo()
            continue
        cur = len(adj)
        if cur > best_cnt:
            best_cnt = cur
            best_E = raw()
            stale = 0

    n, E = lib.relabel(best_E)
    if lib.is_valid(n, E, d, D):
        return n, E
    return None


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (D = 3).
#
# H(m, S) has parts Z_m and Z_m, a_i ~ b_{i+s} for s in S. With |S| = d it is
# d-regular and bipartite; it has diameter 3 iff S - S = Z_m (a difference
# cover). Order 2m, and m <= d(d-1)+1. Search S by annealing on the number of
# uncovered nonzero differences, and bisect on m.
# ----------------------------------------------------------------------------

def _cover(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m, or None on timeout."""
    if m < k:
        return None
    if m == k:
        return list(range(m))
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    it = 0
    T = 0.5
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = rng.choice([0.3, 0.5, 0.8])  # reheat
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        # Remove x's differences.
        for s in others:
            g = (x - s) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = (s - x) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        # Add y's differences.
        for s in others:
            g = (y - s) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = (s - y) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            # Undo: remove y's differences, restore x's.
            for s in others:
                cnt[(y - s) % m] -= 1
                cnt[(s - y) % m] -= 1
            for s in others:
                cnt[(x - s) % m] += 1
                cnt[(s - x) % m] += 1
    return sorted(S)


def _haar_best(k, rng, deadline):
    """Bisect m in [k, k(k-1)+1] for the largest m with a difference cover of size k. Returns (m, S) or None."""
    best = None
    lo = k
    hi = k * (k - 1) + 1
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        remaining = deadline - time.monotonic()
        slice_ = max(2.0, 0.3 * remaining)
        S = _cover(k, mid, rng, min(deadline, time.monotonic() + slice_))
        if S is not None:
            lo = mid
            best = (mid, S)
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4)
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
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.75 * float(time_limit), 42.0)
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

    if D == 3:
        # 1. Arc-extended projective plane graphs (fast; the 394 construction for d = 16).
        arcs = _arc_candidates(d, start + 0.12 * budget, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        if arcs:
            consider(arcs[0][0], arcs[0][1])

        # 2. Haar graphs from difference covers: order 2m, degree d, diameter 3.
        if d >= 2:
            res = _haar_best(d, rng, start + 0.7 * budget)
            if res is not None:
                m, S = res
                n, E = lib.haar_graph(m, S)
                consider(n, E)

        # 3. If the arc graph is still the best, spend remaining time on local search from it.
        if arcs and d >= 8 and best_n == arcs[0][0]:
            n_c, E_c, m_c, pl, lp = arcs[0]
            res = _local_search(n_c, E_c, m_c, pl, lp, d, D, deadline,
                                random.Random(seed * 31 + 7))
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
