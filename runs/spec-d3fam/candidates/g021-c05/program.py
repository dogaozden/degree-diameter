import math
import random
import time

import lib

TIME_FRAC = 0.8      # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve


# ---------------------------------------------------------------- safe bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- new construction
#
# Bipartite Haar graph H(m, S) on Z_m x {0,1}: a_i ~ b_{i+s} for s in S, |S| = d.
# Same-side pairs are at distance 2 exactly when S - S covers Z_m. Then S - S + S
# covers Z_m too, so every cross pair is at distance <= 3. Hence diameter 3 holds
# whenever S - S = Z_m. The order is 2m, so the task is to find a d-element S
# whose difference set covers Z_m with m as large as possible (m <= d(d-1)+1).
# Search: simulated annealing over S with 0 fixed in S (WLOG by translation),
# cost = number of nonzero residues not represented as a difference.

def _cover(m, d, rng, deadline):
    """Find S (size d, containing 0) with S - S = Z_m, or return None at the deadline."""
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    cost = sum(1 for r in range(1, m) if cnt[r] == 0)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    step = 0
    frac = 0.0
    while cost:
        step += 1
        if step & 255 == 0:
            now = time.monotonic()
            if now > deadline:
                return None
            frac = (now - t0) / span
        i = rng.randrange(1, d)          # index 0 stays fixed at residue 0
        x = S[i]
        v = rng.randrange(1, m)
        if v in inS:
            continue
        old = cost
        # remove x: decrement all differences involving x
        for j in range(d):
            if j != i:
                y = S[j]
                for r in ((x - y) % m, (y - x) % m):
                    cnt[r] -= 1
                    if cnt[r] == 0:
                        cost += 1
        # add v: increment all differences involving v
        for j in range(d):
            if j != i:
                y = S[j]
                for r in ((v - y) % m, (y - v) % m):
                    if cnt[r] == 0:
                        cost -= 1
                    cnt[r] += 1
        delta = cost - old
        temp = 1.0 * (1.0 - frac) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = v
            inS.discard(x)
            inS.add(v)
        else:
            # revert the move exactly
            for j in range(d):
                if j != i:
                    y = S[j]
                    for r in ((v - y) % m, (y - v) % m):
                        cnt[r] -= 1
                        if cnt[r] == 0:
                            cost += 1
            for j in range(d):
                if j != i:
                    y = S[j]
                    for r in ((x - y) % m, (y - x) % m):
                        if cnt[r] == 0:
                            cost -= 1
                        cnt[r] += 1
            cost = old
    return S


def _haar_search(d, start_n, deadline, rng):
    """Increase m from start_n//2 + 1 while covering searches succeed. Returns (n, edges) or None."""
    best = None
    best_n = start_n
    m = max(start_n // 2 + 1, d)
    while m <= d * (d - 1) + 1 and time.monotonic() < deadline:
        S = None
        for _ in range(2):
            now = time.monotonic()
            if now >= deadline:
                break
            budget_end = min(deadline, now + max(0.5, 0.5 * (deadline - now)))
            S = _cover(m, d, rng, budget_end)
            if S is not None:
                break
        if S is None:
            break
        n2, e2 = lib.haar_graph(m, S)
        if n2 > best_n and lib.is_valid(n2, e2, d, 3):
            best_n = n2
            best = (n2, e2)
        m += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2 or D != 3:             # K_{d,d} has diameter 2 (safe for any D >= 2)
        return lib.haar_graph(d, range(d))
    if lib.is_prime_power(d - 1):    # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Safe starting candidates, each verified.
    bases = []
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        bases.append(pg)
    kdd = lib.haar_graph(d, range(d))
    bases.append(kdd)
    valid = [(n, e) for n, e in bases if lib.is_valid(n, e, d, D)]
    if not valid:
        return kdd
    best_n, best_e = max(valid, key=lambda c: c[0])

    # Bold alternative: bipartite Haar graphs with a difference-covering connection set.
    # Any failure keeps the safe base above.
    try:
        found = _haar_search(d, best_n, deadline, rng)
        if found is not None and found[0] > best_n:
            best_n, best_e = found
    except Exception:
        pass

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return kdd
