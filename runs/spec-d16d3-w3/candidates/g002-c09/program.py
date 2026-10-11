import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups (diameter 3).
#
# Group G of order m, connection set S of size d. Vertices a_g and b_h (g, h in G),
# with a_g ~ b_{g s} for s in S. The graph is bipartite, d-regular and left-invariant.
#   * a-a distances are <= 2 iff S S^{-1} = G,
#   * b-b distances are <= 2 iff S^{-1} S = G,
#   * a-b distances are <= 3 once S S^{-1} = G (a_e - b_s - a_{s t^-1} - b_{s t^-1 u}).
# So the search asks for a d-subset S with both S S^{-1} and S^{-1} S equal to G,
# and grows m as far as the Moore-type ceiling m <= d(d-1)+1 allows.
# ----------------------------------------------------------------------------

_STALL = 3000


def _make_group(m1, k2, r):
    """Multiplication and inverse tables for Z_m1 x|_r Z_k2 (element (a,b) coded a*k2+b).

    k2 == 1 gives the cyclic group Z_m1. Needs gcd(r, m1) = 1 and r^k2 = 1 mod m1.
    """
    if k2 == 1:
        N = m1
        mul = [[(x + y) % N for y in range(N)] for x in range(N)]
        inv = [(-x) % N for x in range(N)]
        return mul, inv
    N = m1 * k2
    pw = [pow(r, b, m1) for b in range(k2)]
    parts = [divmod(x, k2) for x in range(N)]
    mul = []
    for x in range(N):
        a, b = parts[x]
        pb = pw[b]
        row = []
        for y in range(N):
            c, dd = parts[y]
            row.append(((a + pb * c) % m1) * k2 + (b + dd) % k2)
        mul.append(row)
    inv = []
    for x in range(N):
        a, b = parts[x]
        nb = (-b) % k2
        inv.append(((-pw[nb] * a) % m1) * k2 + nb)
    return mul, inv


def _groups_of_order(N, rng, cap):
    """A few group structures of order N: the cyclic group plus random semidirect/direct products."""
    opts = []
    for k2 in range(2, N + 1):
        if N % k2:
            continue
        m1 = N // k2
        if m1 < 2:
            continue
        for r in range(1, m1):
            if math.gcd(r, m1) == 1 and pow(r, k2, m1) == 1 % m1:
                opts.append((m1, k2, r))
    rng.shuffle(opts)
    chosen = [(N, 1, 1)] + opts[:max(0, cap - 1)]
    return [_make_group(*o) for o in chosen]


def _cover_cost(S, mul, inv, m):
    """Number of group elements missing from S S^{-1} plus those missing from S^{-1} S. Zero is success."""
    seen_a = bytearray(m)
    seen_b = bytearray(m)
    ca = 0
    cb = 0
    for s in S:
        row = mul[s]
        irow = mul[inv[s]]
        for t in S:
            x = row[inv[t]]  # s t^{-1}
            if not seen_a[x]:
                seen_a[x] = 1
                ca += 1
            y = irow[t]  # s^{-1} t
            if not seen_b[y]:
                seen_b[y] = 1
                cb += 1
    return 2 * m - ca - cb


def _search(k, m, mul, inv, rng, deadline):
    """Local search (swap moves, annealing-style acceptance, restarts) for a k-set with zero cover cost."""
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        inS = bytearray(m)
        for s in S:
            inS[s] = 1
        cost = _cover_cost(S, mul, inv, m)
        best = cost
        since = 0
        T = 0.5
        while cost:
            since += 1
            if since > _STALL:
                break
            if (since & 63) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(k)
            new = rng.randrange(m)
            if inS[new]:
                continue
            old = S[i]
            S[i] = new
            c2 = _cover_cost(S, mul, inv, m)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
                inS[old] = 0
                inS[new] = 1
                if cost < best:
                    best = cost
                    since = 0
            else:
                S[i] = old
        if cost == 0:
            return S
    return None


def _edges(m, S, mul):
    """Bi-Cayley edge list: a_g = g, b_h = m + h, edge a_g - b_{g s} for s in S."""
    E = []
    for g in range(m):
        row = mul[g]
        for s in S:
            E.append((g, m + row[s]))
    return 2 * m, E


def _bicayley_climb(d, deadline, rng, half_floor, consider):
    """Climb m upward from a feasible start, searching a valid S of size d in a group of order m."""
    m_max = d * (d - 1) + 1
    m = max(d, (3 * m_max) // 5, half_floor + 1)
    if m > m_max:
        return
    budget = 0.2
    while m <= m_max and time.monotonic() < deadline:
        groups = _groups_of_order(m, rng, 6)
        found = None
        mul = inv = None
        tries = 0
        while found is None and time.monotonic() < deadline:
            mul, inv = groups[tries % len(groups)]
            dl = min(deadline, time.monotonic() + budget)
            found = _search(d, m, mul, inv, rng, dl)
            tries += 1
            if tries % len(groups) == 0:
                budget = min(budget * 1.5, 15.0)
        if found is None:
            return
        n, e = _edges(m, found, mul)
        consider(n, e)
        m += 1


# ----------------------------------------------------------------------------
# Projective plane base (exact when d-1 is a prime power).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d-1 (degree q+1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best_n, best
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n = n
            best = (n, e)

    if D == 2:
        return best

    # D >= 3 from here on. Projective plane incidence first (exact for d-1 prime power).
    pg = _pg_candidate(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Main search: bi-Cayley graphs with zero cover cost, which have diameter <= 3 <= D.
    if d >= 2:
        _bicayley_climb(d, deadline, rng, best_n // 2, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
