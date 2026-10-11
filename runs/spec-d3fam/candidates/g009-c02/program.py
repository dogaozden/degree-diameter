import math
import random
import time

import lib

TIME_FRAC = 0.80      # fraction of time_limit used before returning
MARGIN = 3.0          # seconds kept in reserve
TEMP = 0.35           # constant annealing temperature for covering search


# ---------------------------------------------------------------- cyclic covering search

def _bump(cnt, m, a, others, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered-difference counts of element a against others.

    Returns the change in the number of uncovered nonzero residues."""
    ch = 0
    for t in others:
        for x in ((a - t) % m, (t - a) % m):
            if sign < 0:
                cnt[x] -= 1
                if cnt[x] == 0:
                    ch += 1
            else:
                if cnt[x] == 0:
                    ch -= 1
                cnt[x] += 1
    return ch


def _search_covering(m, d, rng, deadline):
    """Find a d-subset S of Z_m with S - S = Z_m (every nonzero residue is a difference), or None.

    A Haar graph H(Z_m, S) then has diameter 3 exactly when this holds."""
    if d > m:
        return None
    S = rng.sample(range(m), d)
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    inS = set(S)
    it = 0
    while True:
        if unc == 0:
            return sorted(S)
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        it += 1
        i = rng.randrange(d)
        a = S[i]
        v = rng.randrange(m)
        if v in inS:
            continue
        others = [S[j] for j in range(d) if j != i]
        ch = _bump(cnt, m, a, others, -1) + _bump(cnt, m, v, others, +1)
        if ch > 0 and rng.random() >= math.exp(-ch / TEMP):
            # reject: undo both changes
            _bump(cnt, m, v, others, -1)
            _bump(cnt, m, a, others, +1)
            continue
        unc += ch
        S[i] = v
        inS.discard(a)
        inS.add(v)


def _best_cyclic_haar(d, D, lo, rng, deadline):
    """Scan cyclic Haar graphs H(Z_m, S) with |S| = d for m in [lo, d^2-d+1]; return the largest valid one."""
    hi = d * d - d + 1          # Moore-type limit for diameter-3 Haar graphs
    best = None
    for m in range(max(lo, d), hi + 1):
        now = time.monotonic()
        if now > deadline:
            break
        per = max(0.5, min(5.0, (deadline - now) / 4.0))
        S = _search_covering(m, d, rng, min(deadline, now + per))
        if S is None:
            continue
        n, edges = lib.haar_graph(m, S)
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
    return best


# ---------------------------------------------------------------- safe constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _safe_candidates(d, D):
    cands = []
    if d == 2 and D >= 2:
        n = 2 * D
        cands.append((n, [(i, (i + 1) % n) for i in range(n)]))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))  # order 2(q^2+q+5), degree q+2 = d
        except Exception:
            pass
    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            cands.append(pg)
    if d >= 1:
        cands.append(lib.haar_graph(d, range(d)))        # K_{d,d}, valid for D >= 2
    if d >= 1:
        cands.append((2, [(0, 1)]))                      # K_2, valid for D >= 1
    return cands


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Moore-extremal projective plane for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Safe fallbacks, each verified.
    best = None
    for n, e in _safe_candidates(d, D):
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    if best is None:
        return 1, []

    # Bold attempt for D = 3: search cyclic Haar graphs with S - S = Z_m,
    # which can reach order up to 2(d^2-d+1) (above the Araujo-Lopez record).
    if D == 3:
        haar = _best_cyclic_haar(d, D, best[0] // 2 + 1, rng, deadline)
        if haar is not None and haar[0] > best[0]:
            best = haar

    return best

