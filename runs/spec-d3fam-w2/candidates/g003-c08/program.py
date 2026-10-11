import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy:
#   1. Safe baseline K_{d,d} (diameter 2), upgraded by the best known
#      diameter-3 construction for the parameters (projective plane incidence
#      when d-1 is a prime power, otherwise the Araujo-Pardo-Lopez record
#      family when d-2 is a prime power).
#   2. For D = 3 and no Moore-optimal plane, search bi-Cayley graphs over
#      groups G of order N with a d-subset S satisfying S S^{-1} = G.
#      Vertices a_x, b_y (x, y in G) with a_x ~ b_{x s} for s in S give a
#      d-regular bipartite graph of order 2N. Annealing minimises the number
#      of uncovered group elements. Groups are cyclic and semidirect products
#      Z_m x| Z_k, cycled round-robin.
#   3. Every candidate is checked with lib.is_valid before it replaces the best.
# ----------------------------------------------------------------------------


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _groups(N, rng, cap=8):
    """Cyclic group of order N plus a sample of semidirect products Z_m x| Z_k of order N."""
    out = [lib.cyclic_group(N)]
    specs = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append((m, k, r))
    rng.shuffle(specs)
    for m, k, r in specs[:cap]:
        try:
            out.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return out


def _ratio(N, mul, inv):
    """R[x][y] = x * y^{-1}. The identity is element 0 in both group families used here."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences of v against S[j], j != skip.

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


def _anneal(N, R, d, rng, steps, deadline):
    """Find d distinct elements S with S S^{-1} = G by simulated annealing; None if not found."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[0] = 1  # identity is covered by the diagonal
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        if (it & 2047) == 0 and time.monotonic() >= deadline:
            return None
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


def _search(N, d, rng, deadline):
    """Search for a valid S in some group of order N before the deadline. Returns (group, S) or None."""
    groups = _groups(N, rng)
    tabs = [None] * len(groups)
    rnd = 0
    while time.monotonic() < deadline:
        idx = rnd % len(groups)
        rnd += 1
        if tabs[idx] is None:
            _, mul, inv = groups[idx]
            tabs[idx] = _ratio(N, mul, inv)
        S = _anneal(N, tabs[idx], d, rng, 20000, deadline)
        if S is not None:
            return groups[idx], S
    return None


def _edges(N, S, mul):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S. Each vertex has degree d."""
    return [(x, N + mul(x, s)) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 3.0)
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

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-optimal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2, q a prime power.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bi-Cayley search: order 2N needs S S^{-1} = G with |S| = d, so N <= d(d-1)+1.
    # Search N ascending from just above the current best; each success raises best_n.
    try:
        hi = d * (d - 1) + 1
        N = max(best_n // 2 + 1, d)
        while N <= hi and time.monotonic() < deadline:
            res = _search(N, d, rng, deadline)
            if res is None:
                break
            (_, mul, _), S = res
            consider(2 * N, _edges(N, S, mul))
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
