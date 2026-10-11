import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
RUN_LEN = 60000       # annealing steps per random restart


# ---------------------------------------------------------------- fallback bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _fallback(d, D):
    """Best verified simple construction (never fails validation silently)."""
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                                   # cycle of length 2D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                                   # K_{d,d}
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):     # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    cands = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))   # record construction
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        cands.append(pg)
    cands.append(lib.haar_graph(d, range(d)))

    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    if valid:
        return max(valid, key=lambda c: c[0])
    return 2, [(0, 1)]


# ---------------------------------------------------------------- new construction
#
# Haar graph of the cyclic group Z_m with connection set S (|S| = d):
#   a_i ~ b_{i+s} for s in S.  It is bipartite and d-regular on 2m vertices.
# Walks of length 2 give a-a pairs at offsets s - t, and walks of length 3 cover
# every a-b pair once S - S = Z_m. So diameter <= 3 holds exactly when every
# nonzero residue is a difference s - t with s != t in S. This is a difference
# covering problem, searched here by simulated annealing with incremental counts.
# Each success gives order 2m, which beats the parent's 2m whenever m is larger.

def _cover_search(m, d, rng, deadline):
    """Find S subset of Z_m, |S| = d, with S - S covering all of Z_m \\ {0}; None on timeout."""
    if d * (d - 1) < m - 1:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(m), d)
        inS = [False] * m
        for x in S:
            inS[x] = True
        cnt = [0] * m
        for i in range(d):
            for j in range(d):
                if i != j:
                    cnt[(S[i] - S[j]) % m] += 1
        unc = sum(1 for r in range(1, m) if cnt[r] == 0)

        for it in range(RUN_LEN):
            if unc == 0:
                return sorted(S)
            if it % 2048 == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(d)
            old = S[i]
            x = rng.randrange(m)
            if inS[x]:
                continue

            delta = 0
            # remove contributions of old
            for j in range(d):
                if j != i:
                    r = (old - S[j]) % m
                    cnt[r] -= 1
                    if cnt[r] == 0:
                        delta += 1
                    r2 = (S[j] - old) % m
                    cnt[r2] -= 1
                    if cnt[r2] == 0:
                        delta += 1
            # add contributions of x
            for j in range(d):
                if j != i:
                    r = (x - S[j]) % m
                    if cnt[r] == 0:
                        delta -= 1
                    cnt[r] += 1
                    r2 = (S[j] - x) % m
                    if cnt[r2] == 0:
                        delta -= 1
                    cnt[r2] += 1

            temp = 1.2 * (1.0 - it / RUN_LEN) + 0.05
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                unc += delta
                inS[old] = False
                inS[x] = True
                S[i] = x
            else:
                # undo: remove x contributions, restore old contributions
                for j in range(d):
                    if j != i:
                        cnt[(x - S[j]) % m] -= 1
                        cnt[(S[j] - x) % m] -= 1
                for j in range(d):
                    if j != i:
                        cnt[(old - S[j]) % m] += 1
                        cnt[(S[j] - old) % m] += 1
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)

    best_n, best_e = _fallback(d, D)

    # Haar covering search: only where the projective-plane extremal case does not apply.
    if D == 3 and d >= 3 and not lib.is_prime_power(d - 1):
        rng = random.Random(seed)
        m = best_n // 2 + 1
        while m >= d and time.monotonic() < deadline:
            S = _cover_search(m, d, rng, deadline)
            if S is None:
                break
            n2, e2 = lib.haar_graph(m, S)
            if n2 <= best_n or not lib.is_valid(n2, e2, d, D):
                break
            best_n, best_e = n2, e2
            m += 1

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return 2, [(0, 1)]
