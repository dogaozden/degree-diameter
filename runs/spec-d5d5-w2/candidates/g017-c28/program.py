import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Constructions:
#   * trivial cases (d <= 2, D <= 2) and the projective plane for D = 3;
#   * bi-Cayley lifts over semidirect products Z_m x|_r Z_k (hill-climbing);
#   * a switch-based annealing search that grows a valid bipartite graph one
#     A-vertex and one B-vertex at a time, repairing diameter defects with
#     degree-preserving double-edge swaps. It starts from the best structured
#     graph found so far, so the record is the floor and growth is the attempt
#     to beat it.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
_BIG = 10 ** 9
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, mul, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D, limit=_BIG):
    """Unreached (source, target) pairs from A_0 and B_0 in the bi-Cayley graph A_x ~ B_{xg}, g in S."""
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
        if total > limit:
            return total
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed) to zero unreached pairs."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D, limit=cur)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Return (T, S) for a valid bi-Cayley lift of order N, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Switch-based annealing over bipartite graphs.
# A state is (nA, nB, E): A-vertices 0..nA-1, B-vertices 0..nB-1, E a list of
# (a, b) pairs. Graph vertex ids: A is a, B is nA + b.
# ----------------------------------------------------------------------------

def _to_graph(nA, nB, E):
    return nA + nB, [(a, nA + b) for a, b in E]


def _matrix(nA, nB, E):
    """Float32 matrix I + A of the graph."""
    n = nA + nB
    M = np.eye(n, dtype=np.float32)
    for a, b in E:
        M[a, nA + b] = 1.0
        M[nA + b, a] = 1.0
    return M


def _cost(M, D):
    """Ordered vertex pairs at distance > D (including unreachable). Zero iff valid."""
    n = M.shape[0]
    R = M
    for _ in range(D - 1):
        R = np.minimum(R @ M, 1.0)
    return int(round(n * n - float(R.sum())))


def _apply(M, nA, E, S, i, j, n1, n2):
    """Replace E[i], E[j] by n1, n2, keeping the set S and matrix M in sync."""
    for a, b in (E[i], E[j]):
        S.discard((a, b))
        M[a, nA + b] = 0.0
        M[nA + b, a] = 0.0
    E[i] = n1
    E[j] = n2
    for a, b in (n1, n2):
        S.add((a, b))
        M[a, nA + b] = 1.0
        M[nA + b, a] = 1.0


def _repair(nA, nB, E, S, M, D, rng, deadline):
    """Degree-preserving double-edge swaps with annealing until the diameter is fine or time runs out."""
    cost = _cost(M, D)
    m = len(E)
    T = 0.6
    while cost > 0:
        if time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        _apply(M, nA, E, S, i, j, (a1, b2), (a2, b1))
        c2 = _cost(M, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _apply(M, nA, E, S, i, j, (a1, b1), (a2, b2))
        T = max(0.15, T * 0.9995)
    return cost


def _grow(nA, nB, E, d, rng):
    """Add one A-vertex and one B-vertex joined to d disjoint edges. Returns (nA+1, nB+1, E2, S2) or None."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for i in order:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    newA, newB = nA, nB
    E2 = list(E)
    for i in chosen:
        x, y = E2[i]
        E2[i] = (newA, y)      # new A-vertex takes y
        E2.append((x, newB))   # new B-vertex takes x
    S2 = set(E2)
    return nA + 1, nB + 1, E2, S2


def _sa_growth(d, D, state, moore, rng, deadline, on_success):
    """Repeatedly grow the current valid state by one vertex per side and repair it."""
    nA, nB, E = state
    while time.monotonic() < deadline and 2 * (nA + 1) <= moore:
        g = _grow(nA, nB, E, d, rng)
        if g is None:
            break
        nA2, nB2, E2, S2 = g
        M = _matrix(nA2, nB2, E2)
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, 0.3 * (deadline - now)))
        if _repair(nA2, nB2, E2, S2, M, D, rng, slice_end) == 0:
            nA, nB, E = nA2, nB2, E2
            on_success((nA, nB, E))
    return (nA, nB, E)


def _best_pg(d):
    """Projective plane incidence for the largest prime power q with q + 1 <= d, as a bipartite state."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n2, edges = lib.projective_plane_incidence(q)
            m = n2 // 2
            return m, [(u, v - m) for u, v in edges]
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    state = (d, d, [(a, b) for a in range(d) for b in range(d)])
    best_state = state
    best_n = 2 * d
    if D == 2:
        return _to_graph(*state)

    moore = lib._moore_bound(d, D)

    def consider(st):
        nonlocal best_state, best_n
        n, e = _to_graph(*st)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_state = st
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider((pg[0], pg[0], pg[1]))
        if best_n >= moore:
            return _to_graph(*best_state)

    # Phase 1: bi-Cayley lifts with a window just above the current record.
    bic_deadline = start + 0.4 * budget
    while time.monotonic() < bic_deadline and best_n < moore:
        lo = best_n // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(8)
        res = _search_bicayley(d, D, N, rng, bic_deadline)
        if res is not None:
            T, S = res
            consider((N, N, [(x, T[x][g]) for x in range(N) for g in S]))

    # Phase 2: grow the best graph with annealed switch repair.
    if best_n < moore and time.monotonic() < deadline:
        _sa_growth(d, D, best_state, moore, rng, deadline, consider)

    n, edges = _to_graph(*best_state)
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return _to_graph(d, d, [(a, b) for a in range(d) for b in range(d)])
