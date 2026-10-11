import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: K_{d,d} (diameter 2), projective-plane incidence graphs, and the
# Araujo-Pardo & Lopez record family for d = q + 2.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups G of order N.
#
# S subset of G with |S| = d and identity in S (WLOG). Vertices a_x, b_y
# (x, y in G) with a_x ~ b_{x s} for s in S. Every vertex has degree exactly d
# and the graph is bipartite. If S S^{-1} = G then diameter <= 3, giving order 2N.
#
# Search: simulated annealing over S minimising uncovered group elements,
# over the cyclic group and semidirect products Z_a x| Z_k of order N,
# with restarts. N is searched ascending; a failure at N ends the search.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign > 0) or remove (sign < 0) quotients created by v against S[j], j != skip.

    Returns the change in the number of uncovered group elements.
    """
    change = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for y in (Q[v][b], Q[b][v]):
            if sign > 0:
                if cnt[y] == 0:
                    change -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    change += 1
    return change


def _anneal(N, d, Q, rng, deadline, moves):
    """Find S of size d containing identity 0 with S S^{-1} = G; None on failure or timeout."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    cnt[0] = 1  # identity is always covered
    for j in range(d):
        for k in range(d):
            if j != k:
                cnt[Q[S[j]][S[k]]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.6 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        delta = _delta(cnt, S, idx, old, -1, Q) + _delta(cnt, S, idx, x, 1, Q)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _delta(cnt, S, idx, x, -1, Q)
            _delta(cnt, S, idx, old, 1, Q)
    return None


def _specs(N, rng, cap=16):
    """Candidate groups of order N: cyclic group plus a shuffled sample of Z_a x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    """Return (M, Q): M[x][y] = x*y and Q[x][y] = x*y^{-1} for the group named by spec."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(y) for y in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, Q


def _search_N(N, d, rng, deadline):
    """Search for valid S in some group of order N before deadline. Returns (S, M) or None."""
    specs = _specs(N, rng)
    tables = {}
    attempt = 0
    while time.monotonic() < deadline:
        spec = specs[attempt % len(specs)]
        attempt += 1
        if spec not in tables:
            try:
                tables[spec] = _tables(spec, N)
            except Exception:
                tables[spec] = None
        tab = tables[spec]
        if tab is None:
            continue
        M, Q = tab
        S = _anneal(N, d, Q, rng, deadline, 20000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, d, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.5)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Known record family for d = q + 2, q a prime power.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
    except Exception:
        pass

    # Bi-Cayley search: ascending N so each success raises the order.
    try:
        hi = d * (d - 1) + 1
        N = max(best[0] // 2 + 1, d)
        while N <= hi:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _search_N(N, d, rng, now + 0.6 * (deadline - now))
            if res is None:
                break
            S, M = res
            consider((2 * N, _edges_from(N, d, S, M)))
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
