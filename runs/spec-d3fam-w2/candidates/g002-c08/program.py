import math
import random
import time

import lib


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
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# --------------------------------------------- new: annealed PG(2,q) extension

def _sa_extend(d, q, t, rng, deadline):
    """Start from PG(2,q) (degree q+1 = d-1, one spare slot per vertex), add t points
    and t lines, then anneal edge swaps to drive the number of pairs at distance > 3
    to zero. Returns (n, edges) on success, else None."""
    n0, e0 = lib.projective_plane_incidence(q)
    m = n0 // 2
    PA = m + t                      # side A: points (0..PA-1)
    n = 2 * PA                      # side B: lines (PA..n-1)

    adj = [set() for _ in range(n)]

    def add(u, v):
        adj[u].add(v)
        adj[v].add(u)

    def rem(u, v):
        adj[u].discard(v)
        adj[v].discard(u)

    for p, l in e0:                 # p < m, l = m + j
        add(p, PA + (l - m))

    pairs = [(a, b) for a in range(PA) for b in range(PA, n)]
    rng.shuffle(pairs)
    for a, b in pairs:              # use the spare slots at random
        if b not in adj[a] and len(adj[a]) < d and len(adj[b]) < d:
            add(a, b)

    full = (1 << n) - 1
    bit = [1 << v for v in range(n)]

    def cost():
        R1 = [0] * n
        for v in range(n):
            r = bit[v]
            for u in adj[v]:
                r |= bit[u]
            R1[v] = r
        R2 = [0] * n
        for v in range(n):
            r = R1[v]
            for u in adj[v]:
                r |= R1[u]
            R2[v] = r
        bad = 0
        for v in range(n):
            r = R2[v]
            for u in adj[v]:
                r |= R2[u]
            bad += (full & ~r).bit_count()
        return bad // 2

    cur = cost()
    if cur == 0:
        return n, [(a, b) for a in range(PA) for b in adj[a] if b >= PA]

    T0, T1 = 1.5, 0.05
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    T = T0
    it = 0
    while cur > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)

        a = rng.randrange(PA)
        b = rng.randrange(PA, n)
        if b in adj[a]:
            continue
        removed = []
        if len(adj[a]) >= d:
            c = rng.choice(tuple(adj[a]))
            rem(a, c)
            removed.append((a, c))
        if len(adj[b]) >= d:
            c = rng.choice(tuple(adj[b]))
            rem(c, b)
            removed.append((c, b))
        add(a, b)
        new = cost()
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            rem(a, b)
            for x, y in removed:
                add(x, y)

    if cur == 0:
        return n, [(a, b) for a in range(PA) for b in adj[a] if b >= PA]
    return None


# ------------------------------------- parent's group search (non-target cases)

def _group_list(N, rng):
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
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _search(N, R, d, rng, steps, deadline):
    S = rng.sample(range(N), d)

    def uncovered(S):
        return N - len({R[a][b] for a in S for b in S})

    cost = uncovered(S)
    T = 0.6
    for _ in range(steps):
        if cost == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        new = uncovered(S)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


def _group_search(d, fb_n, fb_e, rng, deadline):
    lo = fb_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append([N, mul, inv, None])

    best = None
    best_N = lo - 1
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            N, mul, inv, R = job
            if job[0] <= best_N:
                continue
            if R is None:
                R = _ratio_table(N, mul, inv)
                job[3] = R
            S = _search(N, R, d, rng, 1200, deadline)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > fb_n and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_N = N
                jobs = [j for j in jobs if j[0] > best_N]
                break
        jobs = [j for j in jobs if j[0] > best_N]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    fb_n, fb_e = _fallback(d, D)
    if not lib.is_valid(fb_n, fb_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return fb_n, fb_e

    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            res = _sa_extend(d, q, 5, rng, deadline)
        except Exception:
            res = None
        if res is not None and res[0] > fb_n and lib.is_valid(res[0], res[1], d, D):
            return res
        return fb_n, fb_e

    best = _group_search(d, fb_n, fb_e, rng, deadline)
    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return fb_n, fb_e
