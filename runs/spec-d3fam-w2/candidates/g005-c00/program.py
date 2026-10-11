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


def _mul_tables(N, rng, count):
    """Multiplication tables MUL[x][y] of the cyclic group and some semidirect products of order N."""
    tables = [[[(x + y) % N for y in range(N)] for x in range(N)]]
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    for m, k, r in cands[:max(0, count - 1)]:
        _, mul, _ = lib.semidirect_group(m, k, r)
        tables.append([[mul(x, y) for y in range(N)] for x in range(N)])
    return tables


# ---- difference-cover search (cyclic/semidirect Haar lifts, base = 2 vertices) ----

def _upd(cnt, R, S, skip, v, sign):
    """Add/remove ordered differences of v against S[j], j != skip; return change in uncovered count."""
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
    """Find d distinct S with S S^{-1} = G by annealing; None if not found."""
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


def _diff_cover_attempt(N, MUL, d, rng):
    """One annealing attempt for a difference cover of size d in the group with table MUL."""
    inv = [MUL[y].index(0) for y in range(N)]
    R = [[MUL[x][inv[y]] for y in range(N)] for x in range(N)]
    S = _anneal(N, R, d, rng, 6000, R[0][0])
    if S is None:
        return None
    return [[0, 0, g] for g in S]


# ---- new: general fiber-transitive lifts over a base with a vertices per side ----
#
# Base: a A-vertices and a B-vertices, d-regular bipartite multigraph given as darts
# (i, j, g) (union of d random perfect matchings). Lift vertices: A(i,x) = i*N + x,
# B(j,y) = (a+j)*N + y. Dart (i,j,g) joins A(i,x) to B(j, x*g) for every x.
# Left translations are automorphisms, so distances from (u, e) for the 2a base
# vertices u determine the diameter. Cost = number of vertices not within distance 3.

def _random_darts(a, d, N, rng):
    darts, used = [], set()
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            j = perm[i]
            g = rng.randrange(N)
            for _t in range(50):
                if (i, j, g) not in used:
                    break
                g = rng.randrange(N)
            used.add((i, j, g))
            darts.append([i, j, g])
    return darts, used


def _adj(a, N, MUL, darts):
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        bj = (a + j) * N
        for x in range(N):
            u = i * N + x
            v = bj + MUL[x][g]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _uncovered(a, N, adj):
    V = 2 * a * N
    reach = [1 << v for v in range(V)]
    for _ in range(3):
        nxt = []
        for v in range(V):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(V - reach[u * N].bit_count() for u in range(2 * a))


def _anneal_lift(a, d, N, MUL, rng, steps, deadline):
    """Simulated annealing over darts; returns darts with zero uncovered count, or None."""
    darts, used = _random_darts(a, d, N, rng)
    m = len(darts)
    cur = _uncovered(a, N, _adj(a, N, MUL, darts))
    for it in range(steps):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - it / steps) + 0.05
        k = rng.randrange(m)
        i, j, g = darts[k]
        if rng.random() < 0.6:
            g2 = rng.randrange(N)
            n1 = (i, j, g2)
            if g2 == g or n1 in used:
                continue
            new = [(k, n1)]
        else:
            k2 = rng.randrange(m)
            if k2 == k:
                continue
            i2, j2, g2 = darts[k2]
            n1 = (i, j2, g)
            n2 = (i2, j, g2)
            if n1 == n2 or n1 in used or n2 in used:
                continue
            new = [(k, n1), (k2, n2)]
        old = [(kk, tuple(darts[kk])) for kk, _ in new]
        for _, t in old:
            used.discard(t)
        for kk, t in new:
            darts[kk] = list(t)
            used.add(t)
        nc = _uncovered(a, N, _adj(a, N, MUL, darts))
        delta = nc - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = nc
        else:
            for _, t in new:
                used.discard(t)
            for kk, t in old:
                darts[kk] = list(t)
                used.add(t)
    return darts if cur == 0 else None


def _edges(a, N, MUL, darts):
    out = set()
    for i, j, g in darts:
        for x in range(N):
            out.add((i * N + x, (a + j) * N + MUL[x][g]))
    return sorted(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
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

    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    if best_n >= lib.moore_bound(d, D):
        return best

    limit = lib.moore_bound(d, D)
    tables = {}

    def group_tables(N):
        if N not in tables:
            tables[N] = _mul_tables(N, rng, 4)
        return tables[N]

    # Search even orders T = 2aN above the current best, in increasing order.
    T = 2 * (best_n // 2 + 1)
    fails = 0
    while T <= limit and fails < 2 and time.monotonic() < deadline:
        slice_end = time.monotonic() + 0.6 * max(0.0, deadline - time.monotonic())
        cands = []
        for a in (2, 3, 4, 1):
            if T % (2 * a) == 0 and T // (2 * a) >= d:
                cands.append((a, T // (2 * a)))
        found = None
        while found is None and cands and time.monotonic() < slice_end:
            for a, N in cands:
                if time.monotonic() >= slice_end:
                    break
                MUL = rng.choice(group_tables(N))
                if a == 1:
                    S = _diff_cover_attempt(N, MUL, d, rng)
                    darts = [[0, 0, g] for g in S] if S is not None else None
                else:
                    darts = _anneal_lift(a, d, N, MUL, rng, 1500, slice_end)
                if darts is not None:
                    found = (a, N, MUL, darts)
                    break
        if found is None:
            fails += 1
        else:
            a, N, MUL, darts = found
            consider(2 * a * N, _edges(a, N, MUL, darts))
            fails = 0
        T += 2

    return best
