import itertools
import math
import random
import time

import lib

T_HOT = 2.0        # annealing start temperature (unreached-pair units)
T_COLD = 0.05      # annealing end temperature
CAY_ITERS = 400    # bi-Cayley annealing steps per (group, connection set)
CAY_GROUPS = 6     # semidirect groups tried per order in stage 1
STAGE1_FRAC = 0.3  # share of the budget spent on the bi-Cayley stage


# ----------------------------------------------------------------------------
# Stage 1: bi-Cayley search over semidirect products (the parent's family),
# kept as a hedge so the program never falls below the parent's order.
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cay_unreached(N, T, invs, S, D):
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


def _cay_anneal(N, T, invs, d, D, rng, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cay_unreached(N, T, invs, S, D)
    for it in range(CAY_ITERS):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / CAY_ITERS)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cay_unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _cay_try(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:CAY_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _cay_anneal(N, T, invs, d, D, rng, deadline)
        if S is not None:
            return [(x, N + T[x][g]) for x in range(N) for g in S]
    return None


# ----------------------------------------------------------------------------
# Stage 2 (bold change): simulated annealing over general d-regular bipartite
# graphs with double-edge switches. Cost = number of unordered vertex pairs at
# distance > D, computed with bitset ball expansion. No group structure assumed.
# ----------------------------------------------------------------------------

def _bad(N, E, D):
    n2 = 2 * N
    nb = [[] for _ in range(n2)]
    for a, b in E:
        nb[a].append(N + b)
        nb[N + b].append(a)
    reach = [1 << v for v in range(n2)]
    for _ in range(D):
        new = [0] * n2
        for v in range(n2):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n2 - r.bit_count() for r in reach) // 2


def _init(N, d, rng):
    while True:
        S = set()
        E = []
        ok = True
        for _ in range(d):
            perm = None
            for _try in range(60):
                cand = list(range(N))
                rng.shuffle(cand)
                if all((a, cand[a]) not in S for a in range(N)):
                    perm = cand
                    break
            if perm is None:
                ok = False
                break
            for a in range(N):
                S.add((a, perm[a]))
                E.append((a, perm[a]))
        if ok:
            return E, S


def _anneal(N, d, D, rng, budget, deadline):
    E, S = _init(N, d, rng)
    M = len(E)
    cur = _bad(N, E, D)
    t0 = time.monotonic()
    end = min(deadline, t0 + budget)
    span = max(end - t0, 1e-6)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        T = T_HOT * (T_COLD / T_HOT) ** ((now - t0) / span)
        i = rng.randrange(M)
        j = rng.randrange(M)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        new = _bad(N, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Safe baseline: a single edge is valid for any d >= 1, D >= 1.
    consider(2, [(0, 1)])
    if D == 1 or d == 1:
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    # Complete bipartite K_{d,d}: diameter 2, valid for D >= 2.
    consider(*lib.haar_graph(d, range(d)))

    Nmax = lib._moore_bound(d, D) // 2   # per-side size bound
    if Nmax < d + 1:
        return best

    # Stage 1: bi-Cayley hedge. Find the largest order found quickly.
    cay_N = None
    t1 = start + STAGE1_FRAC * (deadline - start)
    N = max(d + 1, Nmax // 2)
    while N >= d + 1 and time.monotonic() < t1:
        res = _cay_try(N, d, D, rng, min(t1, time.monotonic() + 3.0))
        if res is not None:
            consider(2 * N, res)
            cay_N = N
            break
        N -= 1

    # Stage 2: general bipartite annealing, starting just above stage 1.
    N = (cay_N + 1) if cay_N is not None else max(d + 1, Nmax // 2 - 1)
    while time.monotonic() < deadline and d + 1 <= N <= Nmax:
        rem = deadline - time.monotonic()
        budget = max(1.0, 0.35 * rem)
        E = _anneal(N, d, D, rng, budget, deadline)
        if E is not None:
            consider(2 * N, [(a, N + b) for a, b in E])
            N += 1
        else:
            N -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
