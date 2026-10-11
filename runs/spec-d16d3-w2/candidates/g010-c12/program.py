import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: bi-Cayley (Haar-type) graphs over a group G of order N.
#
# Vertices a_g and b_g for g in G. Connection set S with |S| = d gives edges
# a_g ~ b_{g s} for s in S. Same-side pairs are at distance 2 exactly when
# every non-identity element of G lies in S S^{-1} (on the A side) and in
# S^{-1} S (on the B side). Cross pairs are then at distance <= 3. So the
# problem becomes a difference-cover search: find a d-subset S of G covering
# G with S S^{-1}, for the largest possible |G|.
#
# The projective-plane-based construction of the parent is replaced here by
# this covering search, which can exceed the 2*197 record for d = 16 and
# does not depend on the existence of a projective plane.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_table(N, rng):
    """Return (M, inv) for a random group of order N: multiplication table and inverses.

    Identity is coded 0. Either cyclic Z_N or a semidirect product Z_m x| Z_k.
    """
    options = []
    for k in range(2, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            options.append((m, k, rs))
    if options and rng.random() < 0.6:
        m, k, rs = rng.choice(options)
        r = rng.choice(rs)
        _, mul, _ = lib.semidirect_group(m, k, r)
    else:
        def mul(x, y):
            return (x + y) % N
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    inv = [M[x].index(0) for x in range(N)]
    return M, inv


def _cost(S, M, inv, N):
    """Number of uncovered non-identity elements on the A side plus on the B side. Zero is good."""
    A = set()
    B = set()
    for s in S:
        Ms = M[s]
        Is = inv[s]
        for t in S:
            A.add(Ms[inv[t]])   # s t^{-1}
            B.add(M[Is][t])     # s^{-1} t
    A.discard(0)
    B.discard(0)
    return 2 * (N - 1) - len(A) - len(B)


def _search(N, d, M, inv, deadline, rng):
    """Simulated annealing for a d-subset S of G with zero cost. Returns S or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    c = _cost(S, M, inv, N)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = 1.5
    it = 0
    while c > 0:
        it += 1
        if (it & 63) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - start) / span
            T = 1.5 * (0.02 ** frac)
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(S, M, inv, N)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c = c2
        else:
            S[i] = old
    return list(S) if c == 0 else None


def _graph(N, M, S):
    """Bipartite graph on 2N vertices: a_g = g, b_x = N + x, edges a_g ~ b_{g s} for s in S."""
    edges = []
    for g in range(N):
        row = M[g]
        for s in S:
            edges.append((g, N + row[s]))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    if D == 2:
        return best

    # D >= 3: projective plane incidence is a valid diameter-3 candidate.
    pg = _best_pg(d)
    if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
        best = pg

    # Main search: difference covers of groups of order N with |S| = d.
    # Target: 2N > 394 for d = 16. The random walk moves N up after each success.
    N = max(d + 1, int(0.83 * (d * d - d + 1)))
    fails = {}
    found_any = False
    while time.monotonic() < deadline - 0.2:
        now = time.monotonic()
        remaining = deadline - now
        chunk = min(remaining, max(1.0, budget / 8.0))
        M, inv = _group_table(N, rng)
        S = _search(N, d, M, inv, now + chunk, rng)
        if S is not None:
            n, e = _graph(N, M, S)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                found_any = True
            N += 1
        else:
            fails[N] = fails.get(N, 0) + 1
            # Before any success, back off if this order keeps failing.
            if not found_any and fails[N] >= 3 and N > d + 1:
                N -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
