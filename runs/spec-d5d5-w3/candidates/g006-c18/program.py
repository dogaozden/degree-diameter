import math
import random
import time

import lib

S_CHOICES = (2, 3, 4, 1)   # base-graph sizes per side (s=1 is the plain bi-Cayley case)
ANNEAL_ITERS = 1500        # annealing steps per restart
RESTARTS = 3               # fresh random states per (s, N, group)
GROUPS_PER_TRY = 12        # groups of order N tried per attempt
NEAR_WINDOW = 3            # orders N tried above the current threshold


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base multigraphs over finite groups.
#
# Base graph: s "A" vertices and s "B" vertices. For each of d matchings j we
# have a permutation perm_j of range(s) and a voltage volt_j[i] in G, giving the
# base dart A_i -> B_{perm_j[i]} with voltage volt_j[i]. The lift has vertices
# (A_i, x) and (B_b, y) for x, y in G, and edges (A_i, x) -- (B_b, x*g).
# Each A and B fiber has degree d. Left multiplication is an automorphism, so
# distances from (A_i, e) and (B_b, e) determine the diameter.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic when k = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, m, k, r):
    """Multiplication table T[x][g] = x*g and inverse list for the group, identity = 0."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _cost(s, N, D, T, invs, perms, volts):
    """Total number of (source, vertex) pairs at distance > D, over sources A_0..A_{s-1}, B_0..B_{s-1}."""
    sN = s * N
    total_V = 2 * sN
    out = [[] for _ in range(s)]
    inn = [[] for _ in range(s)]
    for j in range(len(perms)):
        p = perms[j]
        v = volts[j]
        for i in range(s):
            b = p[i]
            g = v[i]
            out[i].append((b, g))
            inn[b].append((i, invs[g]))
    bad = 0
    sources = [i * N for i in range(s)] + [sN + b * N for b in range(s)]
    for src in sources:
        seen = bytearray(total_V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < sN:
                    i, x = divmod(u, N)
                    Tx = T[x]
                    for b, g in out[i]:
                        w = sN + b * N + Tx[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    b, y = divmod(u - sN, N)
                    Ty = T[y]
                    for i, gi in inn[b]:
                        w = i * N + Ty[gi]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        bad += total_V - count
    return bad


def _anneal(s, d, N, D, T, invs, rng, deadline):
    """Simulated annealing over permutations and voltages until every source reaches everything within D."""
    perms = [rng.sample(range(s), s) for _ in range(d)]
    volts = [[rng.randrange(N) for _ in range(s)] for _ in range(d)]
    cur = _cost(s, N, D, T, invs, perms, volts)
    for it in range(ANNEAL_ITERS):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.5, 3.0 * (1.0 - it / ANNEAL_ITERS))
        j = rng.randrange(d)
        if s > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(s), 2)
            p = perms[j]
            p[a], p[b] = p[b], p[a]
            v = _cost(s, N, D, T, invs, perms, volts)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                p[a], p[b] = p[b], p[a]
        else:
            i = rng.randrange(s)
            old = volts[j][i]
            volts[j][i] = rng.randrange(N)
            v = _cost(s, N, D, T, invs, perms, volts)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volts[j][i] = old
    if cur == 0:
        return perms, volts
    return None


def _try_order(s, N, d, D, rng, deadline):
    """Try several groups of order N with several annealing restarts each."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, m, k, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            res = _anneal(s, d, N, D, T, invs, rng, deadline)
            if res is not None:
                perms, volts = res
                return T, perms, volts
    return None


def _edges(s, N, T, perms, volts):
    """Lift the base graph to an explicit edge list on 2*s*N vertices."""
    sN = s * N
    edges = set()
    for j in range(len(perms)):
        for i in range(s):
            b = perms[j][i]
            g = volts[j][i]
            for x in range(N):
                u = i * N + x
                w = sN + b * N + T[x][g]
                edges.add((min(u, w), max(u, w)))
    return sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if d >= 2 and D >= 2:
        # Safe baseline: complete bipartite K_{d,d} (diameter 2).
        consider(*lib.haar_graph(d, range(d)))

        moore = lib.moore_bound(d, D)
        budget = 2.0
        while time.monotonic() < deadline:
            cand = []
            for s in S_CHOICES:
                Nlo = max(best[0] // (2 * s) + 1, moore // (4 * s), 1)
                Nhi = min(moore // (2 * s), Nlo + NEAR_WINDOW)
                for N in range(Nlo, Nhi + 1):
                    cand.append((s, N))
            if not cand:
                break
            rng.shuffle(cand)
            done = False
            for s, N in cand:
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _try_order(s, N, d, D, rng, min(deadline, now + budget))
                if res is not None:
                    T, perms, volts = res
                    consider(2 * s * N, _edges(s, N, T, perms, volts))
                    done = True
                    break
            if not done:
                budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
