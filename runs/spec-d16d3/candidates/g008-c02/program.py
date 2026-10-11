import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane bases and arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# NEW (bold): difference-cover Haar graphs for diameter 3.
#
# The Haar graph H(m, S) has a_i ~ b_{i+s} for s in S, |S| = d, so it is d-regular
# with 2m vertices. Same-side distances are even, so a_0 to a_y needs y in S-S
# (distance 2). Opposite-side distances are odd and need reach 1 or 3. If S-S
# covers all of Z_m, then S-S+S = Z_m too (since S-S+u covers Z_m for any u in S),
# so the diameter is at most 3. Hence any difference cover of size d in Z_m gives a
# valid graph with 2m vertices, and m <= d^2 - d + 1 (the Moore-type bound).
# The record 394 = 2*197 corresponds to m = 197 for d = 16; the ceiling is m = 241.
# ----------------------------------------------------------------------------

def _swap(S, cnt, idx, c, m):
    """Replace S[idx] by c, updating ordered-difference counts; return the change in uncovered residues."""
    a = S[idx]
    delta = 0
    for j in range(len(S)):
        if j == idx:
            continue
        b = S[j]
        x = (a - b) % m
        y = (b - a) % m
        cnt[x] -= 1
        if cnt[x] == 0:
            delta += 1
        cnt[y] -= 1
        if cnt[y] == 0:
            delta += 1
    S[idx] = c
    for j in range(len(S)):
        if j == idx:
            continue
        b = S[j]
        x = (c - b) % m
        y = (b - c) % m
        if cnt[x] == 0:
            delta -= 1
        cnt[x] += 1
        if cnt[y] == 0:
            delta -= 1
        cnt[y] += 1
    return delta


def _dc_anneal(k, m, rng, deadline):
    """Anneal a k-set S in Z_m (0 in S) with S-S = Z_m. Returns S or None."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for i in range(k):
        for j in range(i + 1, k):
            x = (S[i] - S[j]) % m
            cnt[x] += 1
            cnt[(m - x) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while unc > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 0.6 * (0.02 ** ((now - t0) / span))
        idx = rng.randrange(1, k)
        if rng.random() < 0.5:
            missing = [x for x in range(1, m) if cnt[x] == 0]
            x = rng.choice(missing)
            c = (x + S[rng.randrange(k)]) % m  # creates difference x with some element
        else:
            c = rng.randrange(1, m)
        if c in S:
            continue
        old = S[idx]
        d1 = _swap(S, cnt, idx, c, m)
        if d1 <= 0 or rng.random() < math.exp(-d1 / T):
            unc += d1
        else:
            _swap(S, cnt, idx, old, m)
    return S


def _search_dc(k, deadline, rng, consider):
    """Climb m upward from a fraction of the bound, keeping every success."""
    bound = k * k - k + 1
    m = max(k + 1, int(0.75 * bound))
    fails = 0
    while m <= bound:
        now = time.monotonic()
        avail = deadline - now
        if avail <= 0.2:
            break
        budget = min(6.0, max(0.5, 0.12 * avail))
        S = _dc_anneal(k, m, rng, min(deadline, now + budget))
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)
            m += 1
            fails = 0
        else:
            fails += 1
            if fails >= 4:
                break


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D == 2:
        return best

    # Cheap constructions first.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    for n_c, e_c in _arc_extensions(d, start + 0.15 * time_limit,
                                    random.Random(seed * 7919 + d)):
        consider(n_c, e_c)

    # Bold primary search: difference-cover Haar graphs (diameter 3, valid for any D >= 3).
    if d >= 3:
        dc_end = deadline if D == 3 else start + 0.4 * time_limit
        _search_dc(d, dc_end, rng, consider)

    # Secondary search for larger D: annealed group voltage lifts.
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
