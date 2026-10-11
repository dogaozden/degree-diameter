import math
import random
import time

import lib


MAX_GROUPS = 12        # groups tried per order N in one bi-Cayley attempt
ITERS = 600            # annealing steps per (group, connection set) try
T_HOT = 1.5            # bi-Cayley annealing start temperature
T_COLD = 0.15          # bi-Cayley annealing end temperature
ATT_START = 0.5        # seconds per bi-Cayley attempt at first
ATT_CAP = 4.0          # cap on per-attempt seconds
STAGE_A_FRAC = 0.35    # budget fraction spent on structured bi-Cayley search
EXT_T0 = 4.0           # edge-switch repair annealing start temperature
EXT_T1 = 0.3           # edge-switch repair annealing end temperature
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Stage A: bi-Cayley lifts over Z_m x|_r Z_k with annealed connection sets.
# Vertices A_x, B_y (x, y in G); A_x ~ B_{x g} for g in S, |S| = d.
# Left translations are automorphisms, so checking eccentricities of A_0 and B_0
# is enough for diameter D.
# ----------------------------------------------------------------------------

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
    """Cached (order, T, invs): T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
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


def _anneal_bicayley(N, T, invs, d, D, rng, iters, deadline):
    """Anneal S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt_bicayley(N, d, D, rng, deadline):
    """Try groups of order N until one yields a valid connection set."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, T, invs = _tables(m, k, r)
        S = _anneal_bicayley(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Stage B (bold change): grow a d-regular bipartite graph by one vertex per
# side, then repair it by degree-preserving edge switches (2-switch moves on
# the bipartite edge set) with simulated annealing on the number of
# ordered vertex pairs at distance > D. Runs on top of the best bi-Cayley base.
# ----------------------------------------------------------------------------

def _bad_ordered(n, adj, D):
    """Ordered pairs (u, v) with dist > D, via bitmask ball growth."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _grow_regular(N, E, d, rng):
    """Add one left and one right vertex to a d-regular bipartite graph on N+N vertices.

    Pick d edges (l_i, r_i) with distinct l_i and distinct r_i; replace each by
    (new_left, r_i) and (l_i, new_right). Result is d-regular on (N+1)+(N+1).
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    usedl, usedr, pick = set(), set(), []
    for i in order:
        l, r = E[i]
        if l in usedl or r in usedr:
            continue
        usedl.add(l)
        usedr.add(r)
        pick.append(i)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    ps = set(pick)
    out = [E[i] for i in range(len(E)) if i not in ps]
    a = N
    for i in pick:
        l, r = E[i]
        out.append((a, r))
        out.append((l, N))
    return N + 1, out


def _anneal_regular(M, E0, D, rng, deadline):
    """Edge-switch annealing on a d-regular bipartite graph with M vertices per side.

    Left vertex l is vertex l; right vertex r is vertex M + r.
    Returns a list of (l, r) pairs with zero bad pairs, or None.
    """
    Es = [[l, r] for l, r in E0]
    S = {(l, r) for l, r in E0}
    n = 2 * M
    adj = [[] for _ in range(n)]
    for l, r in E0:
        adj[l].append(M + r)
        adj[M + r].append(l)
    m_e = len(Es)

    def sw(i, j):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Self-inverse on the index pair."""
        a1, b1 = Es[i]
        a2, b2 = Es[j]
        adj[a1].remove(M + b1)
        adj[M + b1].remove(a1)
        adj[a2].remove(M + b2)
        adj[M + b2].remove(a2)
        adj[a1].append(M + b2)
        adj[M + b2].append(a1)
        adj[a2].append(M + b1)
        adj[M + b1].append(a2)
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        Es[i] = [a1, b2]
        Es[j] = [a2, b1]

    cost = _bad_ordered(n, adj, D)
    if cost == 0:
        return [tuple(e) for e in Es]

    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - start) / span)
        T = EXT_T0 * (EXT_T1 / EXT_T0) ** frac
        i = rng.randrange(m_e)
        j = rng.randrange(m_e)
        if i == j:
            continue
        a1, b1 = Es[i]
        a2, b2 = Es[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        sw(i, j)
        c2 = _bad_ordered(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost == 0:
                return [tuple(e) for e in Es]
        else:
            sw(i, j)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # K_{d,d}: valid for D >= 2.
    consider(*lib.haar_graph(d, range(d)))
    if D == 1:
        consider(2, [(0, 1)])
        return best
    if D == 2:
        return best

    # Known optimal construction for D = 3 when d - 1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2:
        return best
    Nmax = moore // 2

    # Stage A: bi-Cayley search, keeping the largest regular base found.
    base = None
    stageA_end = start + STAGE_A_FRAC * budget
    window = 6
    att = ATT_START
    fails = 0
    try:
        while time.monotonic() < stageA_end:
            lo = max(d + 1, best[0] // 2 + 1)
            if lo > Nmax:
                break
            hi = min(Nmax, lo + window)
            N = rng.randint(lo, hi)
            att_end = min(stageA_end, time.monotonic() + att)
            res = _attempt_bicayley(N, d, D, rng, att_end)
            if res is not None:
                T, S = res
                E = [(x, T[x][g]) for x in range(N) for g in S]
                base = (N, E)
                consider(2 * N, [(x, N + y) for x, y in E])
                fails = 0
            else:
                fails += 1
                if fails % 4 == 0:
                    window = min(window + 4, Nmax)
                    att = min(ATT_CAP, att * 1.3)
    except Exception:
        pass

    # Stage B: grow the regular base by one vertex per side and repair by edge switches.
    if base is not None:
        try:
            cur_N, cur_E = base
            while time.monotonic() < deadline:
                if 2 * (cur_N + 1) > moore:
                    break
                grown = _grow_regular(cur_N, cur_E, d, rng)
                if grown is None:
                    break
                M, E0 = grown
                now = time.monotonic()
                rem = deadline - now
                slice_end = min(deadline, now + max(2.0, 0.6 * rem))
                E1 = _anneal_regular(M, E0, D, rng, slice_end)
                if E1 is not None:
                    cur_N, cur_E = M, E1
                    consider(2 * M, [(l, M + r) for l, r in E1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
