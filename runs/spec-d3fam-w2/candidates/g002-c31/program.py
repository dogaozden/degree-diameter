import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe fallbacks and base constructions.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))            # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)      # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


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
# Cover-based vertex extension and edge saturation (used on PG(2,q)).
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
# Repair growth: insert two vertices by annealed matching swaps (diameter 3).
# ----------------------------------------------------------------------------

def _repair_add_pair(n, edges, d, D, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    Ecol = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    m_e = len(Ecol)
    if m_e < d:
        return None

    order = list(range(m_e))
    rng.shuffle(order)
    M = []
    usedA, usedB = set(), set()
    for j in order:
        a, b = Ecol[j]
        if a in usedA or b in usedB:
            continue
        M.append(j)
        usedA.add(a)
        usedB.add(b)
        if len(M) == d:
            break
    if len(M) < d:
        return None

    def build_pair(Mlist):
        rem = set(Mlist)
        out = [Ecol[j] for j in range(m_e) if j not in rem]
        x, y = n, n + 1
        for j in Mlist:
            a, b = Ecol[j]
            out.append((x, b))
            out.append((a, y))
        return n + 2, out

    def cost(Mlist):
        nn, out = build_pair(Mlist)
        return lib.bad_pairs(nn, out, D)

    cur = cost(M)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0 = 1.0
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - start) / span
        T = T0 * (0.02 ** frac)
        p = rng.randrange(d)
        old = M[p]
        a_old, b_old = Ecol[old]
        Mset = set(M)
        j = None
        for _ in range(60):
            c = rng.randrange(m_e)
            if c in Mset:
                continue
            a, b = Ecol[c]
            if a != a_old and a in usedA:
                continue
            if b != b_old and b in usedB:
                continue
            j = c
            break
        if j is None:
            continue
        a, b = Ecol[j]
        M2 = M[:]
        M2[p] = j
        c2 = cost(M2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            usedA.discard(a_old)
            usedB.discard(b_old)
            usedA.add(a)
            usedB.add(b)
            M = M2
            cur = c2

    if cur == 0:
        return build_pair(M)
    return None


# ----------------------------------------------------------------------------
# Difference-cover lifts: two base vertices a, b; darts (a, b, s) for s in S.
# The graph on G x {0,1} with a_x ~ b_{x s} has diameter <= 3 whenever
# S S^{-1} = G, and order 2|G| with |G| <= d(d-1)+1.
# ----------------------------------------------------------------------------

def _group_list(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k of order N."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _dc_swap(cnt, R, S, i, y, uncov):
    """Replace S[i] by y, updating ordered-pair counts cnt and the uncovered count."""
    x = S[i]
    for j, s in enumerate(S):
        if j == i:
            continue
        for g in (R[x][s], R[s][x]):
            cnt[g] -= 1
            if cnt[g] == 0:
                uncov += 1
    g = R[x][x]
    cnt[g] -= 1
    if cnt[g] == 0:
        uncov += 1
    for j, s in enumerate(S):
        if j == i:
            continue
        for g in (R[y][s], R[s][y]):
            if cnt[g] == 0:
                uncov -= 1
            cnt[g] += 1
    g = R[y][y]
    if cnt[g] == 0:
        uncov -= 1
    cnt[g] += 1
    S[i] = y
    return uncov


def _dc_search(N, R, d, rng, steps, deadline):
    """Annealing search for d distinct elements S with S S^{-1} = G (cost = uncovered count)."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    for a in S:
        for b in S:
            cnt[R[a][b]] += 1
    uncov = sum(1 for c in cnt if c == 0)
    T = 0.5
    for step in range(steps):
        if uncov == 0:
            return S
        if (step & 255) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        y = rng.randrange(N)
        if y in S:
            continue
        x = S[i]
        new = _dc_swap(cnt, R, S, i, y, uncov)
        if new <= uncov or rng.random() < math.exp(-(new - uncov) / T):
            uncov = new
        else:
            _dc_swap(cnt, R, S, i, x, new)
    return S if uncov == 0 else None


def _dc_stage(best_n, d, D, deadline, rng):
    """Round-robin over (group, order) jobs, largest orders first. Returns best (n, edges) or None."""
    lo = best_n // 2 + 1
    hi = d * (d - 1) + 1
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng):
            jobs.append([N, mul, inv, None])

    found = None
    best_N = lo - 1
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            N, mul, inv, R = job
            if N <= best_N:
                continue
            if R is None:
                R = _ratio_table(N, mul, inv)
                job[3] = R
            S = _dc_search(N, R, d, rng, 1500, deadline)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > 2 * best_N and lib.is_valid(n, edges, d, D):
                found = (n, edges)
                best_N = N
                jobs = [j for j in jobs if j[0] > best_N]
                break
        jobs = [j for j in jobs if j[0] > best_N]
    return found


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products, annealed (used for D >= 4).
# ----------------------------------------------------------------------------

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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []

    best_n, best_e = _fallback(d, D)
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3 and d >= 3 and not lib.is_prime_power(d - 1):
        # Plain projective plane, grown by cover extension (cheap, may add vertices).
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.10 * budget, rng)
            consider(n2, e2)

        # Difference-cover lifts: aim for order 2|G| above the current best.
        found = _dc_stage(best_n, d, D, start + 0.70 * budget, rng)
        if found is not None:
            consider(found[0], found[1])

        # Repair growth from the best graph found so far.
        t_end = start + 0.92 * budget
        cur = (best_n, best_e)
        while time.monotonic() < t_end:
            r = _repair_add_pair(cur[0], cur[1], d, D, t_end, rng)
            if r is None or not lib.is_valid(r[0], r[1], d, D):
                break
            cur = r
            consider(r[0], r[1])

    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.4 * budget, rng)
            consider(n2, e2)

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

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
