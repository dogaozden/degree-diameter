import math
import random
import time

import lib

TIME_FRAC = 0.85       # fraction of time_limit used before returning
MARGIN = 2.5           # seconds kept in reserve
ITER_PER_GROUP = 1200  # annealing steps per (group, order) attempt
GROUPS_PER_ORDER = 2   # groups tried for each order m
MAX_FAILS = 4          # consecutive orders without success before stopping
CAP_LIMIT = 400        # cap on group order (keeps tables small)


# ---------------------------------------------------------------- Haar-graph search
#
# The Haar graph H(G, S) of a group G with connection set S (|S| = d) has vertices
# (g,0), (h,1) for g,h in G, with (g,0) ~ (g*s,1) for s in S. It is d-regular and
# bipartite on 2|G| vertices. Left multiplication by G is an automorphism acting
# transitively on each side, so the diameter is at most D iff every vertex of side 0
# and every vertex of side 1 reaches all others within D. It is enough to run BFS
# from (e,0) and (e,1).

def _bad(N, mt, S, Sinv, D):
    """Number of vertices NOT within distance D of (e,0) or (e,1). Zero iff diameter <= D."""
    total = 0
    M = 2 * N
    for src in (0, N):
        seen = bytearray(M)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            if not frontier:
                break
            nxt = []
            for x in frontier:
                if x < N:                      # side 0: g -> side 1, g*s
                    row = mt[x]
                    for s in S:
                        y = N + row[s]
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
                else:                          # side 1: h -> side 0, h*s^-1
                    row = mt[x - N]
                    for si in Sinv:
                        y = row[si]
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
            reached += len(nxt)
            frontier = nxt
        total += M - reached
    return total


def _anneal(N, mt, iv, d, D, budget, rng, deadline):
    """Search for a d-subset S of the group with Haar graph diameter <= D."""
    S = rng.sample(range(N), d)
    Sinv = [iv[s] for s in S]
    inS = set(S)
    cost = _bad(N, mt, S, Sinv, D)
    for it in range(budget):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in inS:
            continue
        S2 = S[:]
        S2[i] = g
        Sinv2 = Sinv[:]
        Sinv2[i] = iv[g]
        new = _bad(N, mt, S2, Sinv2, D)
        delta = new - cost
        temp = 0.8 * (1.0 - it / budget) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            inS.discard(S[i])
            inS.add(g)
            S, Sinv, cost = S2, Sinv2, new
    return S if cost == 0 else None


def _groups_of_order(m, rng):
    """Cyclic group plus some semidirect products Z_a x|_r Z_b with a*b = m."""
    cands = [lib.cyclic_group(m)]
    for a in range(2, m):
        if m % a:
            continue
        b = m // a
        if b < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        rng.shuffle(rs)
        for r in rs[:2]:
            cands.append(lib.semidirect_group(a, b, r))
    rng.shuffle(cands)
    return cands[:GROUPS_PER_ORDER]


def _haar_edges(m, mt, S):
    edges = []
    for g in range(m):
        row = mt[g]
        for s in S:
            edges.append((g, m + row[s]))
    return 2 * m, edges


def _consider(best, n, e, d, D):
    """Keep (n, e) if it is valid and larger than the current best."""
    if n > best[0] and lib.is_valid(n, e, d, D):
        best[0], best[1] = n, e
        return True
    return False


def _haar_search(d, D, rng, best, deadline):
    cap = sum((d - 1) ** i for i in range(D))   # half the Moore bound
    cap = min(max(cap, d), CAP_LIMIT)
    m = max(d, int(0.75 * cap))
    fails = 0
    while m <= cap and fails < MAX_FAILS and time.monotonic() < deadline:
        ok = False
        for order, mul, inv in _groups_of_order(m, rng):
            if time.monotonic() > deadline:
                break
            mt = [[mul(x, y) for y in range(m)] for x in range(m)]
            iv = [inv(x) for x in range(m)]
            S = _anneal(m, mt, iv, d, D, ITER_PER_GROUP, rng, deadline)
            if S is not None:
                n, e = _haar_edges(m, mt, S)
                _consider(best, n, e, d, D)
                ok = True
                break
        fails = 0 if ok else fails + 1
        m += 1


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

    best = [0, []]

    # Safe fallback: K_{d,d} (diameter 2 <= D).
    n, e = lib.haar_graph(d, range(d))
    _consider(best, n, e, d, D)

    if D == 3:
        # Moore-extremal projective plane when d-1 is a prime power.
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            if _consider(best, n, e, d, D):
                return best[0], best[1]
        # Largest prime power q <= d-1 gives degree q+1 <= d.
        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2:
            n, e = lib.projective_plane_incidence(q)
            _consider(best, n, e, d, D)
        # Araujo-Pardo & Lopez record construction for d = q+2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                _consider(best, n, e, d, D)
            except Exception:
                pass

    # Main search: Haar graphs of groups of order m, pushed upward in m.
    try:
        _haar_search(d, D, rng, best, deadline)
    except Exception:
        pass

    if best[0] == 0:
        return 1, []
    return best[0], best[1]
