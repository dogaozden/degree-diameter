import random
import time

import lib


# ----------------------------------------------------------------------------
# Bitset bi-Cayley search over cyclic groups.
#
# A lift graph has vertices A_x and B_x for x in Z_N, with A_x ~ B_{x+s} for
# s in S, |S| = d, and 0 in S (WLOG by translation). Left translation is an
# automorphism, so the diameter is at most D iff BFS from A_0 and from B_0
# reaches every vertex within D steps. Each BFS layer is kept as an N-bit
# integer, and a shift by s is a cyclic rotation of that integer. This is a
# different search engine from the per-pair BFS used before: it evaluates
# candidate connection sets with a few bit operations per layer, so far more
# candidates fit in the time budget.
# ----------------------------------------------------------------------------


def _rot(F, s, N, mask):
    """Bitmask F with every bit x moved to (x + s) mod N."""
    if s == 0:
        return F
    return ((F << s) | (F >> (N - s))) & mask


def _unreached(N, S, D, mask):
    """Number of (source, vertex) pairs at distance > D, for sources A_0 and B_0."""
    negS = [(N - s) % N for s in S]
    total = 0
    for start_a in (True, False):
        if start_a:
            seen_a, seen_b, fa, fb = 1, 0, 1, 0
        else:
            seen_a, seen_b, fa, fb = 0, 1, 0, 1
        for _ in range(D):
            nb = 0
            for s in S:
                nb |= _rot(fa, s, N, mask)
            nb &= ~seen_b & mask
            na = 0
            for s in negS:
                na |= _rot(fb, s, N, mask)
            na &= ~seen_a & mask
            if not na and not nb:
                break
            seen_a |= na
            seen_b |= nb
            fa, fb = na, nb
        total += 2 * N - seen_a.bit_count() - seen_b.bit_count()
    return total


def _climb(N, d, D, rng, iters, deadline):
    """Plateau-walking hill climb on S (containing 0) to zero unreached pairs."""
    mask = (1 << N) - 1
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, S, D, mask)
    for _ in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, S2, D, mask)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _cyclic_lift_edges(N, S):
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Structured baselines for small diameters.
# ----------------------------------------------------------------------------

def _structured_d3(d):
    """Projective-plane incidence graphs; Araujo-Pardo & Lopez when d-2 is a prime power."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            break
    if d - 2 >= 3 and lib.is_prime_power(d - 2) and not lib.is_prime_power(d - 1):
        try:
            out.append(lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass
    return out


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, fb_e)
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        for n_c, e_c in _structured_d3(d):
            consider(n_c, e_c)

    rng = random.Random(seed * 1000003 + 17 * d + D)

    # Sweep cyclic bi-Cayley orders upward from the smallest order that beats
    # the current best. Each order gets a few random restarts before moving on.
    maxN = moore // 2
    N = max(2, best[0] // 2 + 1)
    restarts_per_N = 8
    while best[0] < moore and time.monotonic() < deadline and N <= maxN:
        N = max(N, best[0] // 2 + 1)
        if N > maxN:
            break
        found = None
        for _ in range(restarts_per_N):
            if time.monotonic() > deadline:
                break
            S = _climb(N, d, D, rng, 400, deadline)
            if S is not None:
                found = S
                break
        if found is not None:
            consider(2 * N, _cyclic_lift_edges(N, found))
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
