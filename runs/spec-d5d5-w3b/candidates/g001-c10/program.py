import math
import random
import time

import lib

T_HOT = 2.5        # initial annealing temperature (unreached-pair units)
T_COLD = 0.05      # final annealing temperature
DUP_PEN = 40       # penalty per repeated (u, v, g) dart
ITERS = 6000       # annealing steps per attempt (also capped by time)
A_CHOICES = (1, 2, 3)  # base vertices per side; 2*a*M total vertices


# ----------------------------------------------------------------------------
# Multi-vertex voltage lifts over semidirect products Z_m x| Z_k.
#
# Base bipartite multigraph: a A-vertices, a B-vertices, d darts per base
# vertex (so each base vertex has degree d). Each dart (u, v, g) joins
# A_{u,x} to B_{v, x*g} for all x in G, where |G| = M. Left multiplication by
# G is an automorphism that acts transitively on each fibre, so the diameter
# is decided by eccentricities of one representative per base vertex.
#
# Vertex indexing: A_{u,x} -> u*M + x; B_{v,y} -> a*M + v*M + y.
# Identity of the semidirect coding is element 0.
# ----------------------------------------------------------------------------

def _groups(M):
    """Return semidirect parameters (m, k, r) with m*k = M."""
    out = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(M, params):
    """Multiplication table MT[x][g] = x*g for the group with the given parameters."""
    m, k, r = params
    _, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(M)] for x in range(M)]


def _evaluate(darts, a, D, M, MT):
    """Return (cost, dup): cost = unreached pairs from representatives + penalty for repeated darts."""
    NT = 2 * a * M
    off = a * M
    adj = [[] for _ in range(NT)]
    seen = set()
    dup = 0
    for u, v, g in darts:
        key = (u, v, g)
        if key in seen:
            dup += 1
        else:
            seen.add(key)
        for x in range(M):
            p = u * M + x
            q = off + v * M + MT[x][g]
            adj[p].append(q)
            adj[q].append(p)
    cost = 0
    reps = [u * M for u in range(a)] + [off + v * M for v in range(a)]
    for s in reps:
        dist = [-1] * NT
        dist[s] = 0
        frontier = [s]
        reached = 1
        for depth in range(1, D + 1):
            nxt = []
            for x in frontier:
                for y in adj[x]:
                    if dist[y] < 0:
                        dist[y] = depth
                        nxt.append(y)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        cost += NT - reached
    return cost + DUP_PEN * dup, dup


def _edges(darts, a, M, MT):
    """Expand darts into the explicit edge list of the lift."""
    off = a * M
    out = []
    for u, v, g in darts:
        for x in range(M):
            out.append((u * M + x, off + v * M + MT[x][g]))
    return out


def _anneal(a, D, M, MT, d, rng, deadline):
    """Anneal dart voltages and B-endpoints until all representative eccentricities are <= D."""
    Ast = [u for u in range(a) for _ in range(d)]
    Bst = [v for v in range(a) for _ in range(d)]
    rng.shuffle(Bst)
    darts = [[Ast[i], Bst[i], rng.randrange(M)] for i in range(a * d)]
    nd = len(darts)
    cur, _ = _evaluate(darts, a, D, M, MT)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        if rng.random() < 0.5:
            i = rng.randrange(nd)
            old = darts[i][2]
            darts[i][2] = rng.randrange(M)
            new, _ = _evaluate(darts, a, D, M, MT)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                darts[i][2] = old
        else:
            i = rng.randrange(nd)
            j = rng.randrange(nd)
            if i == j or darts[i][1] == darts[j][1]:
                continue
            darts[i][1], darts[j][1] = darts[j][1], darts[i][1]
            new, _ = _evaluate(darts, a, D, M, MT)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                darts[i][1], darts[j][1] = darts[j][1], darts[i][1]
    if cur == 0:
        return darts
    return None


# ----------------------------------------------------------------------------
# Fallback families.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 8.0)
    rng = random.Random(seed)

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d < 1 or D < 1:
        return best
    if d == 1 or D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe fallbacks (K_{d,d} has diameter 2).
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Multi-vertex lift search.
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        M_floor = best[0] + 1
        feasible = []
        for a in A_CHOICES:
            M_min = -(-M_floor // (2 * a))
            if 2 * a * M_min <= moore:
                feasible.append((a, M_min))
        if not feasible:
            break
        a, M_min = rng.choice(feasible)
        M = M_min + rng.randrange(3)
        if 2 * a * M > moore:
            M = M_min
        groups = _groups(M)
        params = rng.choice(groups)
        MT = _mul_table(M, params)
        budget = rng.uniform(3.0, 9.0)
        att_deadline = min(deadline, time.monotonic() + budget)
        darts = _anneal(a, D, M, MT, d, rng, att_deadline)
        if darts is not None:
            consider(2 * a * M, _edges(darts, a, M, MT))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
