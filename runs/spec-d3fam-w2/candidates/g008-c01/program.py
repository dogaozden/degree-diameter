import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: K_{d,d} (diameter 2), cycles for d = 2, and the projective plane
# incidence graph when d-1 is a prime power (Moore-optimal for D = 3).
# ----------------------------------------------------------------------------

def _fallback(d, D):
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        return lib.haar_graph(D, [0, 1])  # cycle of length 2D, diameter D
    return lib.haar_graph(d, range(d))    # K_{d,d}, diameter 2


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups of order N.
#
# Let S be a d-subset of G. Vertices a_x, b_y (x, y in G); a_x ~ b_{x s} for s in S.
# Degrees are d and the graph is bipartite. Same-side distance 2 needs S S^{-1} = G,
# and then the cross distance is at most 3, so the diameter is at most 3.
# Order 2N with N <= d(d-1)+1.
#
# Search: annealing on the number of uncovered group elements, with a
# focused move that proposes an element covering a random uncovered g.
# Groups: cyclic plus a sample of semidirect products Z_a x| Z_k.
# ----------------------------------------------------------------------------

def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) the differences of v against S[j], j != skip.

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


def _anneal(N, d, M, R, I, rng, steps, deadline):
    """Find d distinct elements S with S S^{-1} = G; None on failure or timeout."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[0] = 1  # identity is always covered by a_a - b_a - a_a
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        if (it & 1023) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.6 * (1.0 - it / steps) + 0.02
        i = rng.randrange(d)
        if unc > 0 and rng.random() < 0.6:
            g = -1
            for _ in range(30):
                c = rng.randrange(N)
                if cnt[c] == 0:
                    g = c
                    break
            if g < 0:
                x = rng.randrange(N)
            else:
                j = rng.randrange(d - 1)
                if j >= i:
                    j += 1
                b = S[j]
                if rng.random() < 0.5:
                    x = M[g][b]          # x * b^{-1} = g
                else:
                    x = M[I[g]][b]       # b * x^{-1} = g
        else:
            x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, 1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _upd(cnt, R, S, i, x, -1)
            _upd(cnt, R, S, i, old, 1)
    return None


def _specs(N, rng, cap=8):
    """Cyclic group of order N plus a sample of semidirect products Z_a x| Z_k."""
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
    return [("cyc",)] + cands[:cap - 1]


def _tables(spec, N):
    """Multiplication table M, inverse list I, and ratio table R[x][y] = x * y^{-1}."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    R = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, I, R


def _search_N(N, d, rng, deadline):
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None."""
    specs = _specs(N, rng)
    tabs = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in tabs:
            try:
                tabs[spec] = _tables(spec, N)
            except Exception:
                tabs[spec] = None
        tab = tabs[spec]
        if tab is None:
            continue
        M, I, R = tab
        S = _anneal(N, d, M, R, I, rng, 20000, deadline)
        if S is not None:
            return S, M
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
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

    # Only D >= 3 with d >= 3 is searched; everything else uses the baseline.
    if D < 3 or d < 3:
        return best

    # Moore-optimal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    pg = _best_pg(d)
    if pg is not None:
        consider(*pg)

    # Bi-Cayley search: only N with 2N > best_n can improve, so go upward from there.
    try:
        hi = d * (d - 1) + 1
        N = max(best_n // 2 + 1, d)
        while N <= hi and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            res = _search_N(N, d, rng, time.monotonic() + 0.85 * rem)
            if res is None:
                break
            S, M = res
            e = [(x, N + M[x][s]) for x in range(N) for s in S]
            consider(2 * N, e)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
