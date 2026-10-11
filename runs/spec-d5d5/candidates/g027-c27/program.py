import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley lifts over a wider family of groups, searched by
# simulated annealing on the connection set. Groups are semidirect products
# Z_m x|_r Z_k and affine groups AGL(1,q) = GF(q) x| GF(q)*, with order N.
# A lift of order N has 2N vertices, is d-regular, and is bipartite.
#
# Safe fallbacks: K_{d,d} (diameter 2), C_{2D} (d = 2), K_2 (d = 1),
# and the projective-plane incidence graph (diameter 3) when D >= 3.
# Every candidate is checked with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6          # groups tried per order N
ANNEAL_ITERS = 5000     # annealing steps per group
WINDOW = 8              # candidate orders above the current lower bound
PER_ORDER_SECONDS = 2.5 # time slice for one order N
_CACHE = {}


def _group_params(N):
    """Return group descriptors of order N: semidirect (m, k, r) and affine (q)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("semi", m, k, r))
    for q in range(2, N + 2):
        if q * (q - 1) == N and lib.is_prime_power(q):
            out.append(("aff", q))
    return out


def _table(p):
    """Return (N, T, invs) with T[x][g] = x*g, identity 0, and invs[g] = g^-1."""
    hit = _CACHE.get(p)
    if hit is not None:
        return hit
    if p[0] == "semi":
        _, m, k, r = p
        N, mul, _ = lib.semidirect_group(m, k, r)
    else:
        q = p[1]
        F = lib.GF(q)
        MT = F.mul_table.tolist()
        AT = F.add_table.tolist()
        N = q * (q - 1)

        def mul(x, g):
            # Element (a, b) with a in GF(q)*, b in GF(q); coded as (a-1)*q + b.
            xa, xb = divmod(x, q)
            ga, gb = divmod(g, q)
            a = xa + 1
            c = ga + 1
            b = AT[MT[a][gb]][xb]
            return (MT[a][c] - 1) * q + b

    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [T[g].index(0) for g in range(N)]
    val = (N, T, invs)
    if len(_CACHE) >= 8:
        _CACHE.clear()
    _CACHE[p] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs not within distance D, from A_0 and B_0 (zero means valid).

    A_x ~ B_{x g} for g in S. Left translation is an automorphism, so two
    eccentricity checks suffice.
    """
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, deadline, iters):
    """Simulated annealing over S (identity fixed in S, WLOG). Returns S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - it / iters) + 0.05
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _try_order(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid lift, else None."""
    if N < d:
        return None
    params = _group_params(N)
    rng.shuffle(params)
    for p in params[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        NN, T, invs = _table(p)
        S = _anneal(NN, T, invs, d, D, rng, deadline, ANNEAL_ITERS)
        if S is not None:
            return NN, T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective-plane incidence has diameter 3, so it is valid for any D >= 3.
    if best[0] < moore:
        try:
            if lib.is_prime_power(d - 1):
                n, e = lib.projective_plane_incidence(d - 1)
                consider(n, e)
            elif d - 2 >= 3 and lib.is_prime_power(d - 2):
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
        except (ValueError, AssertionError):
            pass

    # Main search: bi-Cayley lifts with order N just above the current record.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(WINDOW)
        sub = min(deadline, time.monotonic() + PER_ORDER_SECONDS)
        res = _try_order(d, D, N, rng, sub)
        if res is not None:
            NN, T, S = res
            edges = [(x, NN + T[x][g]) for x in range(NN) for g in S]
            consider(2 * NN, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
