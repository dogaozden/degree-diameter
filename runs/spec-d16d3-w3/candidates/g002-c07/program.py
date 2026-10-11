import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW (bold): Haar graphs from difference covers.
#
# Bipartite Haar graph H(m, S): a_i ~ b_{i+s} for s in S (subset of Z_m, |S| = d).
# Two a-vertices a_i, a_j have a common neighbour iff i - j lies in S - S. So the
# graph has diameter <= 3 when S - S covers all of Z_m. A "difference cover" of
# size d gives m up to d(d-1)+1, i.e. 2m vertices. A Singer difference set
# reproduces the projective-plane bound, and near-covers can beat the record.
# We find covers by annealing with guided moves.
# ----------------------------------------------------------------------------

def _init_state(m, k, rng):
    """Random set S = {0} + (k-1) residues, with difference counts and uncovered count."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    return S, cnt, unc


def _apply(cnt, others, v, m, sign):
    """Add (sign=+1) or remove (sign=-1) element v against the set `others`.

    Returns the change in the number of uncovered nonzero residues.
    """
    delta = 0
    for u in others:
        a = (v - u) % m
        b = (u - v) % m
        if sign > 0:
            if cnt[a] == 0:
                delta -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                delta -= 1
            cnt[b] += 1
        else:
            cnt[a] -= 1
            if cnt[a] == 0:
                delta += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                delta += 1
    return delta


def _cover_search(m, k, deadline, rng):
    """Find S in Z_m, |S| = k, 0 in S, with S - S = Z_m; None if the deadline passes."""
    if k < 2 or m < k:
        return None
    S, cnt, unc = _init_state(m, k, rng)
    T = 0.4
    it = 0
    while True:
        if unc == 0:
            return sorted(S)
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        if it % 20000 == 0:
            S, cnt, unc = _init_state(m, k, rng)
            continue
        unc_list = [r for r in range(1, m) if cnt[r] == 0]
        r = unc_list[rng.randrange(len(unc_list))]
        i = rng.randrange(1, k)
        old = S[i]
        others = S[:i] + S[i + 1:]
        t = others[rng.randrange(len(others))]
        x = (t + r) % m  # guarantees x - t = r becomes a difference
        if x in others or x == old:
            continue
        d1 = _apply(cnt, others, old, m, -1)
        d2 = _apply(cnt, others, x, m, 1)
        delta = d1 + d2
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
        else:
            _apply(cnt, others, x, m, -1)
            _apply(cnt, others, old, m, 1)


def _best_haar_cover(d, deadline, rng):
    """Binary search for the largest m with a difference cover of size d in Z_m."""
    k = d
    ub = k * (k - 1) + 1
    lo, hi = k, ub
    best = None
    while lo <= hi:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.3:
            break
        mid = (lo + hi + 1) // 2
        budget = max(0.5, min(6.0, 0.25 * remaining))
        S = _cover_search(mid, k, min(deadline, now + budget), rng)
        if S is not None:
            best = (mid, S)
            lo = mid + 1
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# Legacy pipeline (previous parent), kept as a second source of candidates.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_base(d):
    """Araujo-Pardo--Lopez graph for the largest prime power q >= 3 with q + 2 <= d."""
    for q in range(min(d - 2, 40), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except (ValueError, ZeroDivisionError):
                return None
    return None


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
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of a point set S with all loads <= s; returns the largest found."""
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
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new A and a new B vertex per element of S."""
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


def _arc_extensions(d, deadline, rng):
    """Arc-extended projective plane candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
            for attempt in range(30):
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
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


def _pair_anneal(n, edges, d, D, deadline, rng):
    """Return (n+2, edges) with diameter <= D found by switch annealing, or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    spA = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    spB = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    if not spA or not spB:
        return None
    rng.shuffle(spA)
    rng.shuffle(spB)

    EA, EB = [], []
    for u, v in edges:
        if color[u] == 0:
            EA.append(u)
            EB.append(v)
        else:
            EA.append(v)
            EB.append(u)
    a, b = n, n + 1
    kb = min(d - 1, len(spB))
    ka = min(d - 1, len(spA))
    EA.append(a)
    EB.append(b)
    for v in spB[:kb]:
        EA.append(a)
        EB.append(v)
    for u in spA[:ka]:
        EA.append(u)
        EB.append(b)

    N = n + 2
    m = len(EA)
    eset = set(zip(EA, EB))

    def bad():
        return lib.bad_pairs(N, list(zip(EA, EB)), D)

    cost = bad()
    best_cost = cost
    best = (list(EA), list(EB))
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 2.0 * (0.05 ** frac)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        ai, bi, aj, bj = EA[i], EB[i], EA[j], EB[j]
        if ai == aj or bi == bj:
            continue
        n1, n2 = (ai, bj), (aj, bi)
        if n1 in eset or n2 in eset:
            continue
        EB[i], EB[j] = bj, bi
        c2 = bad()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            eset.discard((ai, bi))
            eset.discard((aj, bj))
            eset.add(n1)
            eset.add(n2)
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best = (list(EA), list(EB))
        else:
            EB[i], EB[j] = bi, bj

    if best_cost != 0:
        return None
    return N, list(zip(best[0], best[1]))


def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D < 3:
        return best

    bound = lib._moore_bound(d, D)

    bases = []
    pg = _best_pg(d)
    if pg is not None:
        bases.append(pg)
    ar = _araujo_base(d)
    if ar is not None:
        bases.append(ar)
    if time.monotonic() < start + 0.2 * time_limit:
        bases.extend(_arc_extensions(d, start + 0.2 * time_limit,
                                     random.Random(seed * 7919 + d)))

    for n0, e0 in bases:
        if best_n >= bound:
            break
        consider(n0, e0)
        if time.monotonic() < start + 0.3 * time_limit:
            n2, e2 = _grow(n0, e0, d, D, start + 0.3 * time_limit, rng)
            consider(n2, e2)

    if best_n >= bound:
        return best

    cur_n, cur_e = best
    fails = 0
    while time.monotonic() < deadline - 0.5 and best_n < bound:
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(2.0, 0.35 * remaining))
        res = _pair_anneal(cur_n, cur_e, d, D, slice_end, rng)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            cur_n, cur_e = res
            consider(cur_n, cur_e)
            fails = 0
            continue
        fails += 1
        n2, e2 = _grow(cur_n, cur_e, d, D, deadline, rng)
        if n2 > cur_n and lib.is_valid(n2, e2, d, D):
            cur_n, cur_e = n2, e2
            consider(cur_n, cur_e)
        if fails > 6:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D < 2:
        return best_n, best_e

    # Legacy construction first, with a bounded slice so Haar search gets most of the time.
    legacy_budget = 0.2 * time_limit if D == 3 else 0.85 * time_limit
    try:
        n, e = _legacy_build(d, D, seed, legacy_budget)
        consider(n, e)
    except Exception:
        pass

    # New: Haar graphs of difference covers (diameter 3 when S - S = Z_m).
    if D == 3 and d >= 2:
        try:
            res = _best_haar_cover(d, start + 0.8 * time_limit,
                                   random.Random(seed * 1000003 + d))
            if res is not None:
                m, S = res
                n, e = lib.haar_graph(m, S)
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
