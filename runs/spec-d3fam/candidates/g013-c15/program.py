import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ANNEAL_ITERS = 4000   # annealing steps per group attempt


# ---------------------------------------------------------------- baseline constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _baseline(d, D):
    """Best known safe construction for (d, D); every returned graph is verified."""
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))  # record construction, degree q+2 = d
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
    return max(valid, key=lambda c: c[0])


# ---------------------------------------------------------------- Cayley-Haar search (D = 3)
#
# Bipartite Haar graph of a group G of order N with connection set S (|S| = d):
#   a_x ~ b_{x*s} for s in S.
# It is d-regular on 2N vertices and vertex-transitive on each side (left multiplication
# is an automorphism). So diameter <= 3 holds iff the balls of radius 3 around a_e and b_e
# cover everything. WLOG e is in S (right-multiplying S is an isomorphism).

def _uncovered(N, mt, S, invS):
    """Number of (vertex, missing) pairs when balls of radius 3 around a_e and b_e are taken."""
    total = 0
    for src in (0, N):
        seen = {src}
        frontier = [src]
        for _ in range(3):
            nxt = []
            for v in frontier:
                if v < N:
                    row = mt[v]
                    cand = [N + row[s] for s in S]
                else:
                    row = mt[v - N]
                    cand = [row[t] for t in invS]
                for u in cand:
                    if u not in seen:
                        seen.add(u)
                        nxt.append(u)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - len(seen)
    return total


def _search(N, mt, inv_t, d, rng, t_end):
    """Simulated annealing over connection sets S of size d (containing identity 0)."""
    def cost(S):
        return _uncovered(N, mt, S, [inv_t[s] for s in S])

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = cost(S)
    it = 0
    while cur > 0 and it < ANNEAL_ITERS and time.monotonic() < t_end:
        it += 1
        i = rng.randrange(1, d)
        t = rng.randrange(1, N)
        if t in S:
            continue
        new = S[:]
        new[i] = t
        val = cost(new)
        delta = val - cur
        temp = 2.0 * (1.0 - it / ANNEAL_ITERS) + 0.1
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = new, val
    return S if cur == 0 else None


def _groups(N, rng):
    """A cyclic group of order N plus a few semidirect products Z_m x| Z_k with mk = N."""
    out = [lib.cyclic_group(N)]
    cands = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    for m, k, r in cands[:2]:
        try:
            out.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return out


def _bold(d, base_n, deadline, rng):
    """Search Haar graphs of order 2N for N above half the baseline order. Returns (n, edges) or None."""
    U = d * (d - 1) + 1           # abelian/group Moore-type bound on |S^{-1}S|
    L = base_n // 2 + 1           # only orders that beat the baseline are interesting
    best = None
    for N in range(L, U + 1):
        now = time.monotonic()
        if now > deadline:
            break
        groups = _groups(N, rng)
        if not groups:
            continue
        per_N = max(0.8, min(2.5, (deadline - now) / (U - N + 1)))
        per_group = per_N / len(groups)
        found = None
        for mul_group in groups:
            _, mul, inv = mul_group
            t_end = min(deadline, time.monotonic() + per_group)
            mt = [[mul(x, y) for y in range(N)] for x in range(N)]
            inv_t = [inv(x) for x in range(N)]
            S = _search(N, mt, inv_t, d, rng, t_end)
            if S is not None:
                found = (mt, S)
                break
        if found is not None:
            mt, S = found
            edges = [(x, N + mt[x][s]) for x in range(N) for s in S]
            if lib.is_valid(2 * N, edges, d, 3):
                best = (2 * N, edges)
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
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    base_n, base_e = _baseline(d, D)

    if D == 3 and d >= 4:
        try:
            res = _bold(d, base_n, deadline, rng)
        except Exception:
            res = None
        if res is not None:
            n, edges = res
            if n > base_n and lib.is_valid(n, edges, d, D):
                return n, edges

    return base_n, base_e
