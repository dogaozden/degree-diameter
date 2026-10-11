import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 6   # groups tried per (order N, attempt)
ITERS = 500                  # annealing steps per (group, block assignment)
T_HOT = 2.0                  # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                 # final annealing temperature
MAX_BUDGET = 15.0            # cap on per-order time slice (seconds)


# ----------------------------------------------------------------------------
# Baseline families (cheap, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Two-by-two base bi-Cayley lifts ("block" construction).
#
# Vertices: A_{i,x} (i in {0,1}, x in G) and B_{j,y} (j in {0,1}, y in G), so
# there are 4|G| vertices. Each block (i, j) holds a set S_{ij} of group
# elements and contributes edges A_{i,x} -- B_{j, x*g} for g in S_{ij}.
# Block sizes: |S_00| = |S_11| = p and |S_01| = |S_10| = d - p, with 1 <= p <= d-1.
# Every A and B vertex then has degree exactly d.
#
# Left multiplication by a group element is an automorphism, so the diameter
# can be read off from BFS out of the four sources A_{0,0}, A_{1,0}, B_{0,0}, B_{1,0}.
# ----------------------------------------------------------------------------

def _direct(a, b):
    """Direct product Z_a x Z_b, element (x, y) coded as x*b + y."""
    def mul(u, v):
        u1, u2 = divmod(u, b)
        v1, v2 = divmod(v, b)
        return ((u1 + v1) % a) * b + (u2 + v2) % b

    def inv(u):
        u1, u2 = divmod(u, b)
        return ((-u1) % a) * b + (-u2) % b

    return a * b, mul, inv


def _group_list(N):
    """Groups of order N: cyclic, semidirect Z_m x| Z_k, and direct products Z_a x Z_b."""
    groups = [lib.cyclic_group(N)]
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    groups.append(lib.semidirect_group(m, k, r))
                except ValueError:
                    pass
    for a in range(2, N):
        if N % a == 0 and a <= N // a:
            groups.append(_direct(a, N // a))
    return groups


def _cost(N, T, invs, blocks, D):
    """Total number of (source, vertex) pairs at distance more than D, over the four sources."""
    dA = [[], []]   # dA[i] = list of (j, g)
    dB = [[], []]   # dB[j] = list of (i, g^{-1})
    for (i, j), gs in blocks.items():
        for g in gs:
            dA[i].append((j, g))
            dB[j].append((i, invs[g]))
    N2 = 2 * N
    total = 0
    for src in (0, N, N2, N2 + N):
        seen = bytearray(4 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N2:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dA[i]:
                        v = N2 + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - N2, N)
                    row = T[y]
                    for i, h in dB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 4 * N - count
    return total


def _anneal(N, T, invs, blocks, d, D, rng, iters, deadline):
    """Simulated annealing over the four block sets, minimising unreached pairs."""
    keys = list(blocks.keys())
    cur = _cost(N, T, invs, blocks, D)
    for it in range(iters):
        if cur == 0:
            return blocks
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        gs = blocks[keys[rng.randrange(4)]]
        pos = rng.randrange(len(gs))
        c = rng.randrange(N)
        if c in gs:
            continue
        old = gs[pos]
        gs[pos] = c
        v = _cost(N, T, invs, blocks, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[pos] = old
    return blocks if cur == 0 else None


def _search(N, d, D, rng, deadline):
    """Try groups of order N with random block assignments until diameter <= D is reached."""
    groups = _group_list(N)
    rng.shuffle(groups)
    for order, mul, inv in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        p = rng.randint(1, d - 1)
        blocks = {
            (0, 0): rng.sample(range(N), p),
            (1, 1): rng.sample(range(N), p),
            (0, 1): rng.sample(range(N), d - p),
            (1, 0): rng.sample(range(N), d - p),
        }
        res = _anneal(N, T, invs, blocks, d, D, rng, ITERS, deadline)
        if res is not None:
            return T, res
    return None


def _edges(N, T, blocks):
    """Edge list of the 4N-vertex block lift."""
    E = []
    for (i, j), gs in blocks.items():
        for g in gs:
            for x in range(N):
                E.append((i * N + x, 2 * N + j * N + T[x][g]))
    return 4 * N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Fallbacks, validated before use.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    # Block lift search: order 4N, so N <= Moore bound / 4.
    moore = lib._moore_bound(d, D)
    Nmax = moore // 4
    N = max(d + 1, moore // 8)
    budget = 2.0

    while time.monotonic() < deadline and N <= Nmax:
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _search(N, d, D, rng, att_deadline)
        if res is not None:
            T, blocks = res
            n, e = _edges(N, T, blocks)
            consider(n, e)
            N += 1
            budget = 2.0
        else:
            budget = min(budget * 1.6, MAX_BUDGET)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
