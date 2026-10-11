import math
import random
import time

import lib

TOP_A = 4          # base vertices per side of the voltage lift
MAX_N = 1200       # largest group order tried (tables cost N^2)
ITERS = 300        # annealing steps per (group, voltage assignment) try
MAX_GROUPS = 40    # groups tried per (a, N) attempt
MAX_CANDS = 400    # cap on the (a, N) candidate list


# ----------------------------------------------------------------------------
# Bipartite voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: a "A" vertices and a "B" vertices. Each A vertex has d darts,
# each B vertex receives d darts. A dart (u, v, g) joins A(u, x) to B(v, x*g)
# for every x in G. Left multiplication by G is an automorphism of the lift,
# so distances from A(u, e) and B(v, e) decide the diameter. The lift has
# 2*a*N vertices and is d-regular and bipartite by construction.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, key):
    """Multiplication table and inverse list for the group with the given key."""
    m, k, r = key
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _cost(a, N, T, invs, state, D):
    """Number of (source, vertex) pairs not within distance D, sources = base representatives."""
    out = [[] for _ in range(a)]
    inn = [[] for _ in range(a)]
    for u, v, g in state:
        out[u].append((v, g))
        inn[v].append((u, invs[g]))
    size = 2 * a * N
    total = 0
    for s in range(2 * a):
        seen = bytearray(size)
        seen[s * N] = 1
        frontier = [s * N]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                b, x = divmod(w, N)
                if b < a:
                    for v, g in out[b]:
                        y = (a + v) * N + T[x][g]
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
                else:
                    for u, ig in inn[b - a]:
                        y = u * N + T[x][ig]
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += size - count
    return total


def _anneal(a, d, N, T, invs, D, rng, deadline):
    """Anneal dart voltages and targets until every base source reaches all vertices within D."""
    slots = a * d
    targets = [v for v in range(a) for _ in range(d)]
    while True:
        rng.shuffle(targets)
        state = [(i // d, targets[i], rng.randrange(N)) for i in range(slots)]
        if len(set(state)) == slots:
            break
    cur = _cost(a, N, T, invs, state, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / ITERS))
        new = list(state)
        if rng.random() < 0.6:
            i = rng.randrange(slots)
            u, v, _ = state[i]
            new[i] = (u, v, rng.randrange(N))
        else:
            i, j = rng.randrange(slots), rng.randrange(slots)
            ui, vi, gi = state[i]
            uj, vj, gj = state[j]
            new[i] = (ui, vj, gi)
            new[j] = (uj, vi, gj)
        if len(set(new)) != slots:
            continue
        c = _cost(a, N, T, invs, new, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            state, cur = new, c
    return state if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for an a-vertex-per-side base until one works or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for key in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, key)
        st = _anneal(a, d, N, T, invs, D, rng, deadline)
        if st is not None:
            return T, st
    return None


def _lift(a, N, T, state):
    """Expand the base darts into the bipartite lift; return (n, edges)."""
    edges = []
    for u, v, g in state:
        for x in range(N):
            edges.append((u * N + x, (a + v) * N + T[x][g]))
    return 2 * a * N, edges


# ----------------------------------------------------------------------------
# Entry point.
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

    # Safe baselines.
    if D == 1:
        consider(2, [(0, 1)])
        return best
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best
    consider(*lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2
    if D == 2:
        return best

    # Voltage-lift search: sizes 2*a*N, smallest beating the current best first.
    try:
        M = lib._moore_bound(d, D)
        best_n = best[0]
        cands = []
        for a in range(1, TOP_A + 1):
            lo = max(d, best_n // (2 * a) + 1)
            hi = min(MAX_N, M // (2 * a))
            for N in range(lo, hi + 1):
                cands.append((2 * a * N, a, N))
        cands.sort()
        cands = cands[:MAX_CANDS]

        budget = 1.5
        while time.monotonic() < deadline and cands:
            tried = False
            for size, a, N in cands:
                now = time.monotonic()
                if now >= deadline:
                    break
                if size <= best[0]:
                    continue
                tried = True
                res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
                if res is not None:
                    T, st = res
                    n, e = _lift(a, N, T, st)
                    consider(n, e)
            if not tried:
                break
            budget *= 1.5
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
