import math
import random
import time

import lib

TIME_FRAC = 0.8   # fraction of time_limit used before returning
MARGIN = 2.0      # seconds kept in reserve


# ---------------------------------------------------------------- constructions
# Main new idea: for D = 3, a Haar graph of Z_m with connection set S (|S| = d)
# has diameter 3 whenever S - S covers every nonzero residue of Z_m. It is
# bipartite, has 2m vertices and is d-regular. The search below finds such
# covering sets S for growing m by simulated annealing, which is a construction
# family different from the parent's vertex-addition growth.

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _araujo(d):
    """Araujo-Pardo / Lopez record construction for degree d (needs d-2 a prime power >= 3)."""
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            return None
    return None


def _remove(cnt, others, x, m):
    """Remove the pairs (x, t) for t in others from the difference counts; return change in zero count."""
    dz = 0
    for t in others:
        r = (x - t) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            dz += 1
        r = (t - x) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            dz += 1
    return dz


def _add(cnt, others, x, m):
    """Add the pairs (x, t) for t in others to the difference counts; return change in zero count."""
    dz = 0
    for t in others:
        r = (x - t) % m
        if cnt[r] == 0:
            dz -= 1
        cnt[r] += 1
        r = (t - x) % m
        if cnt[r] == 0:
            dz -= 1
        cnt[r] += 1
    return dz


def _cover_anneal(m, d, rng, deadline):
    """Find S subset of Z_m with |S| = d and S - S covering all nonzero residues, or None at the deadline."""
    ITERS = 40000
    while time.monotonic() < deadline:
        S = rng.sample(range(m), d)
        inS = [False] * m
        for x in S:
            inS[x] = True
        cnt = [0] * m
        for a in S:
            for b in S:
                if a != b:
                    cnt[(a - b) % m] += 1
        zeros = sum(1 for r in range(1, m) if cnt[r] == 0)
        it = 0
        while zeros > 0 and it < ITERS:
            if (it & 1023) == 0 and time.monotonic() > deadline:
                return None
            T = 1.2 * (0.08 / 1.2) ** (it / ITERS)
            i = rng.randrange(d)
            x = S[i]
            others = S[:i] + S[i + 1:]
            y = rng.randrange(m)
            while inS[y]:
                y = rng.randrange(m)
            delta = _remove(cnt, others, x, m) + _add(cnt, others, y, m)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[i] = y
                inS[x] = False
                inS[y] = True
                zeros += delta
            else:
                _remove(cnt, others, y, m)
                _add(cnt, others, x, m)
            it += 1
        if zeros == 0:
            return S
    return None


def _search_haar(d, rng, deadline):
    """Search increasing m for a covering set; return the Haar graph for the largest m found, or None."""
    m = max(d + 1, d * d // 2)
    cap = d * d - d + 1          # perfect difference-set bound
    best = None
    fails = 0
    while m <= cap and fails < 3:
        now = time.monotonic()
        if now >= deadline:
            break
        budget = max(0.5, 0.3 * (deadline - now))
        S = _cover_anneal(m, d, rng, min(deadline, now + budget))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
        m += 1
    if best is None:
        return None
    return lib.haar_graph(best[0], best[1])


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                                   # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                                   # K_{d,d}: extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):     # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Safe fallbacks, each verified.
    cands = [lib.haar_graph(d, range(d))]
    if D == 3:
        ar = _araujo(d)
        if ar is not None:
            cands.append(ar)
        pg = _pg_base(d)
        if pg is not None:
            cands.append(pg)
    best = None
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)

    # Bold route: cyclic Haar graphs from difference-covering sets.
    if D == 3 and d >= 4:
        try:
            hv = _search_haar(d, rng, deadline)
        except Exception:
            hv = None
        if hv is not None and (best is None or hv[0] > best[0]) and lib.is_valid(hv[0], hv[1], d, D):
            best = hv

    return best

