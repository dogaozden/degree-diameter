import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

CAP_N = 3000          # never build bi-Cayley lifts with more than this many group elements
K_MAX = 32            # skip semidirect groups with more than K_MAX blocks (keeps bitsets cheap)
GROUPS_PER_N = 12     # groups tried per order N before moving on
SA_ITERS = 2500       # annealing steps per (group, restart)
STALL_LIMIT = 500     # re-randomize the connection set after this many non-improving steps
N_WINDOW = 8          # orders tried in a window just above the current best


# ----------------------------------------------------------------------------
# Baseline for D = 3: projective plane incidence graph when d-1 is a prime power.
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bitset bi-Cayley engine.
#
# Group G = Z_m x|_r Z_k, element x = (a, b) coded as a*k + b (lib.semidirect_group).
# Vertices A_x and B_y for x, y in G; A_x ~ B_{x g} for g in S, |S| = d, identity in S.
# A set of group elements is stored as k ints: block b is an m-bit mask over a.
# Right multiplication by g = (c, e) sends block b to block (b + e) mod k, rotated by
# r^b * c mod m. Left translation is an automorphism, so BFS from A_0 and B_0 suffices.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, restricted to k <= K_MAX or cyclic."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        if k > K_MAX and k != 1:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _make_group(m, k, r):
    """Return (order, mul, ops, invs, full). ops[g][b] = (target block, rotation) for right mult by g."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    full = (1 << m) - 1
    powers = [pow(r, b, m) for b in range(k)]
    ops = []
    for g in range(order):
        c, e = divmod(g, k)
        ops.append(tuple(((b + e) % k, (powers[b] * c) % m) for b in range(k)))
    invs = [inv(g) for g in range(order)]
    return order, mul, ops, invs, full


def _unreached(N, D, m, k, full, opsS, opsI):
    """Total (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    total = 0
    for start in (0, 1):
        reach = [[0] * k, [0] * k]
        reach[start][0] = 1
        fr = reach[start][:]
        side = start
        for _ in range(D):
            tabs = opsS if side == 0 else opsI
            Y = [0] * k
            for tab in tabs:
                for b in range(k):
                    v = fr[b]
                    if v:
                        t, s = tab[b]
                        if s:
                            v = ((v << s) | (v >> (m - s))) & full
                        Y[t] |= v
            other = reach[1 - side]
            new = [0] * k
            grew = False
            for b in range(k):
                nb = Y[b] & ~other[b]
                if nb:
                    other[b] |= nb
                    new[b] = nb
                    grew = True
            if not grew:
                break
            fr = new
            side ^= 1
        cnt = sum(x.bit_count() for x in reach[0]) + sum(x.bit_count() for x in reach[1])
        total += 2 * N - cnt
    return total


def _anneal(N, d, D, m, k, full, ops, invs, rng, deadline, iters):
    """Search a connection set S (identity included) with zero unreached pairs; None on failure."""
    if N < d:
        return None

    def cost(S):
        opsS = [ops[g] for g in S]
        opsI = [ops[invs[g]] for g in S]
        return _unreached(N, D, m, k, full, opsS, opsI)

    if d == 1:
        S = [0]
        return S if cost(S) == 0 else None

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = cost(S)
    best = cur
    stall = 0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = cost(S2)
        T = 2.0 * (1.0 - it / iters) + 0.2
        if v <= cur or rng.random() < math.exp(-(v - cur) / T):
            S, cur = S2, v
        if cur < best:
            best = cur
            stall = 0
        else:
            stall += 1
        if stall > STALL_LIMIT:
            S = [0] + rng.sample(range(1, N), d - 1)
            cur = cost(S)
            best = cur
            stall = 0
    return S if cur == 0 else None


def _search(N, d, D, rng, deadline):
    """Try several groups of order N; return (m, k, r, mul, S) for a valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N]:
        if time.monotonic() > deadline:
            return None
        order, mul, ops, invs, full = _make_group(m, k, r)
        S = _anneal(N, d, D, m, k, full, ops, invs, rng, deadline, SA_ITERS)
        if S is not None:
            return m, k, r, mul, S
    return None


def _edges_from(N, mul, S):
    """Edges of the bi-Cayley graph: A_x = x, B_y = N + y, A_x ~ B_{x g}."""
    return 2 * N, [(x, N + mul(x, g)) for x in range(N) for g in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)

    if D == 3:
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bitset bi-Cayley lifts with orders above the current best.
    try:
        max_N = min(moore // 2, CAP_N)
        lo = best_n // 2 + 1
        while time.monotonic() < deadline and lo <= max_N and best_n < moore:
            N = min(max_N, lo + rng.randrange(N_WINDOW))
            if N < d:
                lo = N + 1
                continue
            res = _search(N, d, D, rng, deadline)
            if res is None:
                continue
            m, k, r, mul, S = res
            n, E = _edges_from(N, mul, S)
            if lib.is_valid(n, E, d, D) and n > best_n:
                best = (n, E)
                best_n = n
                lo = N + 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
