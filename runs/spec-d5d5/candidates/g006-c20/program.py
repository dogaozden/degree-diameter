import math
import random
import time

import lib

ITERS = 300          # annealing steps per (group, base shape) try
MAX_GROUPS = 8       # groups tried per attempt
PENALTY = 1000       # cost per duplicate parallel dart with equal voltage
WINDOW = 20          # candidate group orders per base size
MIN_BUDGET = 0.25    # seconds per candidate in the first sweep


# ----------------------------------------------------------------------------
# New family: multi-orbit voltage lifts of random d-regular bipartite base
# multigraphs on a + a base vertices, over semidirect products Z_m x| Z_k.
#
# Base: d random permutations p_t of range(a); darts (i, p_t[i]) for each t, i.
# Each dart carries a group voltage. Lift vertices are (orbit, x), x in G,
# and dart (i, j, g) joins A(i, x) to B(j, x*g). Left multiplication by G is
# an automorphism preserving orbits, so the diameter is decided by BFS from one
# representative per orbit. Parallel darts on the same base pair need distinct
# voltages, enforced by a penalty. a = 1 is the classic bi-Cayley search.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_base(a, d, rng):
    """Return d random permutations of range(a) whose union base graph is connected."""
    while True:
        perms = []
        for _ in range(d):
            p = list(range(a))
            rng.shuffle(p)
            perms.append(p)
        parent = list(range(2 * a))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for p in perms:
            for i in range(a):
                parent[find(i)] = find(a + p[i])
        if len({find(v) for v in range(2 * a)}) == 1:
            return perms


def _cost(a, N, T, invs, pairs, volts, D):
    """Number of (orbit representative, vertex) pairs at distance > D, plus duplicate penalties."""
    seen = set()
    out = [[] for _ in range(a)]
    inn = [[] for _ in range(a)]
    dup = 0
    for (i, j), g in zip(pairs, volts):
        key = (i, j, g)
        if key in seen:
            dup += 1
        else:
            seen.add(key)
            out[i].append((j, g))
            inn[j].append((i, invs[g]))
    if dup:
        return PENALTY * dup
    n = 2 * a * N
    total = 0
    for o0 in range(2 * a):
        seen_v = bytearray(n)
        src = o0 * N
        seen_v[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                o, x = divmod(u, N)
                row = T[x]
                if o < a:
                    for j, g in out[o]:
                        v = (a + j) * N + row[g]
                        if not seen_v[v]:
                            seen_v[v] = 1
                            nxt.append(v)
                else:
                    for i, h in inn[o - a]:
                        v = i * N + row[h]
                        if not seen_v[v]:
                            seen_v[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _anneal(a, N, T, invs, pairs, D, rng, iters, deadline):
    """Simulated annealing over dart voltages to reach diameter <= D."""
    L = len(pairs)
    volts = [rng.randrange(N) for _ in range(L)]
    cur = _cost(a, N, T, invs, pairs, volts, D)
    for it in range(iters):
        if cur == 0:
            return volts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        t = rng.randrange(L)
        c = rng.randrange(N)
        if c == volts[t]:
            continue
        old = volts[t]
        volts[t] = c
        v = _cost(a, N, T, invs, pairs, volts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volts[t] = old
    return volts if cur == 0 else None


def _edges(a, N, T, pairs, volts):
    """Expand base darts with voltages into the full lift edge list."""
    edges = []
    for (i, j), g in zip(pairs, volts):
        base_a = i * N
        base_b = (a + j) * N
        for x in range(N):
            edges.append((base_a + x, base_b + T[x][g]))
    return edges


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N and random bases with a orbits per side; return edges or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        perms = _random_base(a, d, rng)
        pairs = [(i, perms[t][i]) for t in range(d) for i in range(a)]
        volts = _anneal(a, N, T, invs, pairs, D, rng, ITERS, deadline)
        if volts is not None:
            return _edges(a, N, T, pairs, volts)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)
    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d < 1 or D < 1:
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    if D < 2 or d < 2:
        return best

    consider(*lib.haar_graph(d, range(d)))

    # Candidate (order, a, N): order = 2*a*N, only orders above the current best.
    moore = lib._moore_bound(d, D)
    cand_set = set()
    for a in (1, 2, 3):
        lo = max(best[0] // (2 * a) + 1, d)
        hi = min(moore // (2 * a), lo + WINDOW)
        for N in range(lo, hi + 1):
            cand_set.add((2 * a * N, a, N))
    cands = sorted(cand_set)

    # Ascending sweep: cheapest orders first; on success, prune to larger orders.
    budget = MIN_BUDGET
    while cands and time.monotonic() < deadline:
        success = False
        for order, a, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            e = _attempt(a, N, d, D, rng, min(deadline, now + budget))
            if e is not None:
                consider(order, e)
                cands = [c for c in cands if c[0] > best[0]]
                success = True
                break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
