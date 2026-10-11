import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


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
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip.

    Returns the change in the number of uncovered group elements.
    """
    ch = 0
    Rv = R[v]
    for j, b in enumerate(S):
        if j == skip:
            continue
        for g in (Rv[b], R[b][v]):
            if sign > 0:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
    return ch


def _anneal(N, R, d, rng, steps, e):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[e] = 1
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        T = 1.0 - 0.95 * it / steps
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _upd(cnt, R, S, i, x, -1)
            _upd(cnt, R, S, i, old, +1)
    return None


def _dc_search(d, best_n, rng, dl, consider):
    """Difference-cover Haar lifts (order 2N, S S^{-1} = G, |S| = d), ascending N, until dl."""
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= dl:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, dl - time.monotonic())
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    mul, inv = groups[idx][1], groups[idx][2]
                    tables[idx] = _ratio_table(N, mul, inv)
                R = tables[idx]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
        idx, S = found
        mul = groups[idx][1]
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
        consider(n, edges)


def _uncovered(M, v, N):
    """Number of vertices at distance > 3 from v, using bitmask adjacency M."""
    b1 = M[v] | (1 << v)
    b2 = b1
    x = b1
    while x:
        low = x & -x
        b2 |= M[low.bit_length() - 1]
        x ^= low
    b3 = b2
    x = b2
    while x:
        low = x & -x
        b3 |= M[low.bit_length() - 1]
        x ^= low
    return N - b3.bit_count()


def _pencil_anneal(q, d, t, rng, end):
    """Extend PG(2,q) incidence (degree q+1 = d-1) by t new point/line pairs.

    Every new vertex gets degree <= d. Old vertices have one spare slot each.
    New points attach only to lines, new lines only to points (keeps bipartiteness).
    Simulated annealing minimises the number of (new vertex, vertex) pairs at distance > 3.
    Returns (N, edges) when every pair is within distance 3, else None at the deadline.
    """
    m = q * q + q + 1
    n0 = 2 * m
    N = n0 + 2 * t
    _, base_edges = lib.projective_plane_incidence(q)
    M = [0] * N
    deg = [0] * N
    for u, v in base_edges:
        M[u] |= 1 << v
        M[v] |= 1 << u
        deg[u] += 1
        deg[v] += 1
    nl = [[] for _ in range(N)]  # neighbour lists of new vertices only
    newv = list(range(n0, N))
    lines_for_newpt = list(range(m, n0)) + list(range(n0 + t, N))
    points_for_newline = list(range(m)) + list(range(n0, n0 + t))

    def is_newpt(v):
        return v < n0 + t

    def add(a, b):
        M[a] |= 1 << b
        M[b] |= 1 << a
        deg[a] += 1
        deg[b] += 1
        if a >= n0:
            nl[a].append(b)
        if b >= n0:
            nl[b].append(a)

    def rem(a, b):
        M[a] &= ~(1 << b)
        M[b] &= ~(1 << a)
        deg[a] -= 1
        deg[b] -= 1
        if a >= n0:
            nl[a].remove(b)
        if b >= n0:
            nl[b].remove(a)

    def pick(v):
        cands = lines_for_newpt if is_newpt(v) else points_for_newline
        for _ in range(60):
            w = cands[rng.randrange(len(cands))]
            if deg[w] < d and w != v and not ((M[v] >> w) & 1):
                return w
        return None

    def cost():
        return sum(_uncovered(M, v, N) for v in newv)

    cur = cost()
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        frac = (now - t0) / span
        T = 1.0 * (1.0 - frac) + 0.02 * frac
        v = newv[rng.randrange(len(newv))]
        if len(nl[v]) < d:
            w = pick(v)
            if w is None:
                continue
            add(v, w)
            new = cost()
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                rem(v, w)
        else:
            u = nl[v][rng.randrange(len(nl[v]))]
            w = pick(v)
            if w is None or w == u:
                continue
            rem(v, u)
            add(v, w)
            new = cost()
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                rem(v, w)
                add(v, u)

    edges = list(base_edges)
    for v in newv:
        for w in nl[v]:
            if w < n0 or v < w:
                edges.append((w, v))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        # Safe record construction first.
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

        # Branch 1: difference-cover Haar lifts (time-capped share).
        now = time.monotonic()
        dc_deadline = now + 0.3 * max(0.0, deadline - now)
        try:
            _dc_search(d, best_n, rng, dc_deadline, consider)
        except Exception:
            pass

        # Branch 2 (bold): extend PG(2,q), q = d-2, by t new point/line pairs,
        # searching for the smallest t that beats the current best order.
        q = d - 2
        base = 2 * (q * q + q + 1)
        t = max(1, (best_n - base) // 2 + 1)
        while t <= 80:
            now = time.monotonic()
            left = deadline - now
            if left < 1.0:
                break
            try:
                res = _pencil_anneal(q, d, t, rng, now + 0.7 * left)
            except Exception:
                res = None
            if res is None or not consider(*res):
                break
            t = (best_n - base) // 2 + 1

    return best
