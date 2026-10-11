import math
import random
import time

import lib

TIME_FRAC = 0.80       # fraction of time_limit used before returning
MARGIN = 2.0           # seconds kept in reserve
ITER = 20000           # hill-climb steps per restart
RESTARTS = 40          # restarts per candidate group order


def _covered(m, S):
    """Number of residues mod m that are differences s - t of S (including 0)."""
    return len({(s - t) % m for s in S for t in S})


def _climb(m, d, rng, iters, deadline):
    """Hill-climb a d-subset S of Z_m whose difference set S - S covers all of Z_m.

    Returns S on success, or None if the budget runs out.
    """
    S = rng.sample(range(m), d)
    inS = set(S)
    cost = m - _covered(m, S)
    for it in range(iters):
        if cost == 0:
            return S
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(m)
        if x in inS:
            continue
        old = S[i]
        S[i] = x
        new = m - _covered(m, S)
        temp = 1.0 * (1.0 - it / iters) + 0.02
        if new <= cost or rng.random() < math.exp(-(new - cost) / temp):
            inS.discard(old)
            inS.add(x)
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


def _haar_cover(d, deadline, rng):
    """Haar graph H(Z_m, S) with S - S = Z_m and |S| = d.

    Such a graph is bipartite, d-regular, and has diameter at most 3:
    a-a and b-b distances are at most 2 (since S - S covers Z_m), and a-b
    distances are at most 3 (since S - S + S covers Z_m).
    Search m from the Moore-type bound d^2 - d + 1 downward.
    """
    hi = d * d - d + 1
    for m in range(hi, d - 1, -1):
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            S = _climb(m, d, rng, ITER, deadline)
            if S is not None:
                return lib.haar_graph(m, S)
    return None


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    # Trivial and calibration cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:  # even cycle of length 2D: bipartite, 2-regular, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:  # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):  # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback candidates, all checked with lib.is_valid.
    candidates = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            candidates.append(lib.araujo_lopez_graph(d - 2))  # record, 2(q^2+q+5)
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        candidates.append(pg)
    candidates.append(lib.haar_graph(d, range(d)))

    best = None
    for n, e in candidates:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)

    # Bold alternative for D = 3: cyclic Haar graph from a difference cover.
    if D == 3:
        try:
            alt = _haar_cover(d, deadline, rng)
        except Exception:
            alt = None
        if alt is not None:
            n, e = alt
            if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
                best = (n, e)

    if best is not None:
        return best
    return lib.haar_graph(d, range(d))
