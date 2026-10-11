import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: multi-orbit bi-Cayley lifts over Z_m, found by annealing.
#
# Vertices are a_i^p and b_j^q for p, q in 0..k-1 and i, j in Z_m. Each set
# S[p][q] of shifts gives the edges a_i^p ~ b_{i+s}^q for s in S[p][q]. For k = 1
# this is the cyclic Haar graph, but k >= 2 gives 2km vertices with the same
# degree budget. Translation by t is an automorphism, so the diameter is at most D
# iff every orbit representative reaches all 2km vertices within D steps. Each
# reachability test is a bitmask BFS over Z_m, and simulated annealing swaps shifts
# to minimise the number of unreached (source, vertex) pairs.
# ----------------------------------------------------------------------------

def _rot(X, s, m, full):
    """Rotate bitmask X (bit i = position i in Z_m) so that bit i moves to i + s."""
    s %= m
    if s == 0:
        return X
    return ((X << s) | (X >> (m - s))) & full


def _orbit_cost(k, m, S, D, full):
    """Total number of unreached (source, vertex) pairs over the 2k orbit representatives."""
    fwd = [[] for _ in range(k)]
    bwd = [[] for _ in range(k)]
    for p in range(k):
        for q in range(k):
            for s in S[p][q]:
                fwd[p].append((q, s))
                bwd[q].append((p, (-s) % m))
    total = 0
    full_count = 2 * k * m
    for side in (0, 1):
        for o in range(k):
            A = [0] * k
            B = [0] * k
            if side == 0:
                A[o] = 1
            else:
                B[o] = 1
            for _ in range(D):
                nA = A[:]
                nB = B[:]
                for p in range(k):
                    Ap = A[p]
                    if Ap:
                        for q, s in fwd[p]:
                            nB[q] |= _rot(Ap, s, m, full)
                for q in range(k):
                    Bq = B[q]
                    if Bq:
                        for p, ns in bwd[q]:
                            nA[p] |= _rot(Bq, ns, m, full)
                A, B = nA, nB
            reached = sum(a.bit_count() for a in A) + sum(b.bit_count() for b in B)
            total += full_count - reached
    return total


def _orbit_search(k, m, d, D, deadline, rng):
    """Anneal shift sets S[p][q] over Z_m so the lift has diameter <= D. Returns S or None."""
    full = (1 << m) - 1
    S = [[set() for _ in range(k)] for _ in range(k)]
    rd = [0] * k   # degree of each a-orbit
    cd = [0] * k   # degree of each b-orbit
    cand = [(p, q, s) for p in range(k) for q in range(k) for s in range(m)]
    rng.shuffle(cand)
    for p, q, s in cand:
        if rd[p] < d and cd[q] < d and s not in S[p][q]:
            S[p][q].add(s)
            rd[p] += 1
            cd[q] += 1

    cur = _orbit_cost(k, m, S, D, full)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    frac = 0.0
    it = 0
    while True:
        if cur == 0:
            return S
        it += 1
        if it % 32 == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = min(1.0, (now - t0) / span)
        T = 1.5 * (0.07 ** frac)

        p = rng.randrange(k)
        q = rng.randrange(k)
        Spq = S[p][q]
        if Spq and len(Spq) < m and rng.random() < 0.6:
            # Swap one shift for an unused one: degrees are unchanged.
            x = rng.choice(tuple(Spq))
            y = rng.randrange(m)
            while y in Spq:
                y = rng.randrange(m)
            Spq.discard(x)
            Spq.add(y)
            new = _orbit_cost(k, m, S, D, full)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                Spq.discard(y)
                Spq.add(x)
        elif rd[p] < d and cd[q] < d and len(Spq) < m:
            # Add a new dart if both endpoints have spare degree.
            y = rng.randrange(m)
            while y in Spq:
                y = rng.randrange(m)
            Spq.add(y)
            rd[p] += 1
            cd[q] += 1
            new = _orbit_cost(k, m, S, D, full)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                Spq.discard(y)
                rd[p] -= 1
                cd[q] -= 1


def _build_graph(k, m, S):
    """Expand the orbit description into (n, edges); a_i^p = p*m+i, b_j^q = k*m+q*m+j."""
    n = 2 * k * m
    edges = []
    for p in range(k):
        for q in range(k):
            for s in S[p][q]:
                for i in range(m):
                    edges.append((p * m + i, k * m + q * m + (i + s) % m))
    return n, edges


# ----------------------------------------------------------------------------
# Driver. Every candidate is checked with lib.is_valid before it can replace the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.82 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

    # Calibration shortcut: PG(2, d-1) incidence graph when d-1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        cand = lib.projective_plane_incidence(d - 1)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Round-robin over orbit counts k. Each k always targets the smallest m that
    # would beat the current best, and its time slice grows after each failure.
    ks = [2, 3, 4, 1]
    state = {k: {'m': None, 'slice': 2.0} for k in ks}
    while time.monotonic() < deadline:
        active = False
        for k in ks:
            if time.monotonic() >= deadline:
                break
            target_m = best[0] // (2 * k) + 1
            if 2 * k * target_m > moore:
                continue
            active = True
            st = state[k]
            if st['m'] != target_m:
                st['m'] = target_m
                st['slice'] = 2.0
            slice_end = min(deadline, time.monotonic() + st['slice'])
            try:
                S = _orbit_search(k, target_m, d, D, slice_end, rng)
            except Exception:
                S = None
            if S is not None:
                n, e = _build_graph(k, target_m, S)
                consider(n, e)
                st['m'] = None
            else:
                st['slice'] *= 1.3
        if not active:
            break
        if best[0] >= moore:
            break

    return best
