import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy.
#
# Group-Haar graphs: for a finite group G of order N and a d-subset S of G,
# vertices A_g and B_g (g in G) with A_g ~ B_{g*s} for s in S. This is
# d-regular, bipartite, and has 2N vertices. Left multiplication is an
# automorphism, so the diameter is determined by the walk-endpoint sets from
# A_e and from B_e. Those sets are found by a local search over S that
# maximises coverage. The group is cyclic or a semidirect product Z_a x|_r Z_k,
# and N grows while a valid S can be found.
#
# Projective-plane and Araujo-Pardo-Lopez bases are kept for D = 3, and
# K_{d,d} is the fallback. Every candidate is checked with lib.is_valid.
# ----------------------------------------------------------------------------


def _best_pg(d, count=1):
    """Incidence graphs of PG(2, q) for the largest prime powers q with q + 1 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            if len(out) == count:
                break
    return out


def _score(S, mt, iv, D):
    """Total coverage (out of 4N) of walk-endpoint sets from A_e and from B_e within distance D."""
    invS = [iv[s] for s in S]
    total = 0
    for start_a in (True, False):
        cA, cB = set(), set()
        side = start_a
        F = {0}
        (cA if side else cB).update(F)
        for _ in range(D):
            if side:
                F = {mt[a][s] for a in F for s in S}
            else:
                F = {mt[b][t] for b in F for t in invS}
            side = not side
            (cA if side else cB).update(F)
        total += len(cA) + len(cB)
    return total


def _hill(N, mul, inv, d, D, rng, deadline, iters):
    """Hill-climb a d-subset S of the group until it covers everything within distance D."""
    mt = [[mul(x, y) for y in range(N)] for x in range(N)]
    iv = [inv(x) for x in range(N)]
    target = 4 * N
    for _ in range(3):
        if time.monotonic() >= deadline:
            return None
        S = rng.sample(range(N), d)
        cur = _score(S, mt, iv, D)
        for _ in range(iters):
            if cur >= target:
                return S
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            T = S[:]
            T[i] = x
            sc = _score(T, mt, iv, D)
            if sc >= cur:
                S, cur = T, sc
        if cur >= target:
            return S
    return None


def _groups(N, rng):
    """(mul, inv) pairs for cyclic and some semidirect groups of order N."""
    _, mul, inv = lib.cyclic_group(N)
    out = [(mul, inv)]
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, k, a) == 1]
        if not rs:
            continue
        pick = rs if len(rs) <= 3 else rng.sample(rs, 3)
        for r in pick:
            _, m2, i2 = lib.semidirect_group(a, k, r)
            out.append((m2, i2))
    rng.shuffle(out)
    return out


def _search(d, D, deadline, rng, moore, on_success):
    """Increase the group order N while a covering d-subset can be found."""
    N = d + 1
    while time.monotonic() < deadline and 2 * N < moore:
        now = time.monotonic()
        level_deadline = min(deadline, now + max(3.0, 0.15 * (deadline - now)))
        cands = _groups(N, rng)
        found, found_mul = None, None
        rounds = 0
        while time.monotonic() < level_deadline and cands:
            mul, inv = cands[rounds % len(cands)]
            rounds += 1
            S = _hill(N, mul, inv, d, D, rng, level_deadline, 300)
            if S is not None:
                found, found_mul = S, mul
                break
        if found is None:
            return
        on_success(N, found, found_mul)
        N += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.8 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    if D == 3:
        for b in _best_pg(d, 2):
            consider(b[0], b[1])
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                b = lib.araujo_lopez_graph(d - 2)
                consider(b[0], b[1])
            except Exception:
                pass
        if best[0] >= moore:
            return best

    def on_success(N, S, mul):
        edges = [(g, N + mul(g, s)) for g in range(N) for s in S]
        consider(2 * N, edges)

    try:
        _search(d, D, deadline, rng, moore, on_success)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
