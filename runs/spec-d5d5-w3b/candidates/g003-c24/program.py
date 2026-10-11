import math
import random
import time

import lib

GROUPS_PER_TRY = 6      # semidirect groups tried per (base, N) attempt
MAX_BASE = 3            # largest base size b (b vertices per side of the base graph)
ANNEAL_ITERS = 1500     # annealing steps per (group, voltage assignment) try
T_HOT = 2.0             # initial annealing temperature (unreached-pair units)
T_COLD = 0.1            # final annealing temperature
BUDGET_START = 1.5      # seconds per (base, N) attempt
BUDGET_CAP = 6.0        # cap on per-attempt seconds


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x|_r Z_k of order N = m * k.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups(N):
    """Return all semidirect parameters (m, k, r) with m * k = N."""
    if N in _GROUP_CACHE:
        return _GROUP_CACHE[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[N] = out
    return out


# ----------------------------------------------------------------------------
# Base multigraphs and voltage lifts over a group.
#
# Base: b "A" vertices and b "B" vertices. M[u][v] = number of darts A_u -> B_v.
# Row and column sums equal d, so every lifted vertex has degree d.
# Lift: A_{u,x} -- B_{v, x*g} for each voltage g in S[u][v] (distinct per pair).
# Left multiplication by h maps (u, x) to (u, h*x) and is an automorphism, so
# eccentricities only need checking from the b A-representatives and b
# B-representatives (identity coset).
# ----------------------------------------------------------------------------

def _connected(M, b):
    parent = list(range(2 * b))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for u in range(b):
        for v in range(b):
            if M[u][v]:
                a, c = find(u), find(b + v)
                if a != c:
                    parent[a] = c
    root = find(0)
    return all(find(i) == root for i in range(2 * b))


def _random_counts(b, d, rng):
    """Random d-regular count matrix (sum of d random permutation matrices), connected support."""
    for _ in range(200):
        M = [[0] * b for _ in range(b)]
        for _ in range(d):
            p = list(range(b))
            rng.shuffle(p)
            for u in range(b):
                M[u][p[u]] += 1
        if _connected(M, b):
            return M
    return None


def _cost(b, N, D, T, invs, S):
    """Total unreached (representative, vertex) pairs at distance > D; 0 means diameter <= D."""
    V = 2 * b * N
    bN = b * N
    dA = [[] for _ in range(b)]
    dB = [[] for _ in range(b)]
    for u in range(b):
        for v in range(b):
            for g in S[u][v]:
                dA[u].append((v, g))
                dB[v].append((u, invs[g]))
    sources = [u * N for u in range(b)] + [bN + v * N for v in range(b)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        reached = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                if w < bN:
                    u, x = divmod(w, N)
                    row = T[x]
                    for v, g in dA[u]:
                        z = bN + v * N + row[g]
                        if not seen[z]:
                            seen[z] = 1
                            nxt.append(z)
                else:
                    v, y = divmod(w - bN, N)
                    row = T[y]
                    for u, ig in dB[v]:
                        z = u * N + row[ig]
                        if not seen[z]:
                            seen[z] = 1
                            nxt.append(z)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += V - reached
    return total


def _anneal(b, N, D, T, invs, M, rng, iters, deadline):
    """Simulated annealing over voltage sets S[u][v] (|S[u][v]| = M[u][v]) to reach cost 0."""
    S = [[rng.sample(range(N), M[u][v]) if M[u][v] else [] for v in range(b)]
         for u in range(b)]
    pairs = [(u, v) for u in range(b) for v in range(b) if M[u][v]]
    cur = _cost(b, N, D, T, invs, S)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        u, v = pairs[rng.randrange(len(pairs))]
        lst = S[u][v]
        i = rng.randrange(len(lst))
        if rng.random() < 0.5:
            p1 = pairs[rng.randrange(len(pairs))]
            p2 = pairs[rng.randrange(len(pairs))]
            a = S[p1[0]][p1[1]][rng.randrange(len(S[p1[0]][p1[1]]))]
            g = S[p2[0]][p2[1]][rng.randrange(len(S[p2[0]][p2[1]]))]
            c = T[a][g]
        else:
            c = rng.randrange(N)
        if c in lst:
            continue
        old = lst[i]
        lst[i] = c
        new = _cost(b, N, D, T, invs, S)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            lst[i] = old
    if cur == 0:
        return S
    return None


GROUP_TRY_ITERS = ANNEAL_ITERS


def _attempt(b, N, d, D, M, rng, deadline):
    """Try several groups of order N with base counts M; return (T, S) on success."""
    groups = list(_groups(N))
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(b, N, D, T, invs, M, rng, GROUP_TRY_ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _lift_edges(b, N, T, S):
    """Edges of the lift; A-vertices are 0..bN-1 and B-vertices are bN..2bN-1."""
    bN = b * N
    E = set()
    for u in range(b):
        for v in range(b):
            for g in S[u][v]:
                for x in range(N):
                    E.add((u * N + x, bN + v * N + T[x][g]))
    return 2 * bN, sorted(E)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = {"n": 1, "e": []}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"] = n
            state["e"] = e

    # Record construction for D = 3, d - 1 a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return state["n"], state["e"]

    # Safe baselines.
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    if d < 2 or D < 2:
        return state["n"], state["e"]

    moore = lib.moore_bound(d, D)
    budget = BUDGET_START

    # Main search: voltage lifts of small base multigraphs over semidirect groups.
    # Each round targets vertex counts strictly above the current best.
    while time.monotonic() < deadline:
        bestV = state["n"]
        cands = []
        for b in range(1, MAX_BASE + 1):
            Nmax = moore // (2 * b)
            Nmin = max(1, (bestV + 1 + 2 * b - 1) // (2 * b))
            if Nmin <= Nmax:
                cands.append((b, Nmin, Nmax))
        if not cands:
            break
        b, lo, hi = cands[rng.randrange(len(cands))]
        # Bias toward the low end of the window: smaller orders succeed more often.
        N = min(hi, lo + int((hi - lo + 1) * rng.random() ** 2))

        M = _random_counts(b, d, rng)
        if M is None or max(max(row) for row in M) > N:
            continue

        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(b, N, d, D, M, rng, att_deadline)
        if res is not None:
            T, S = res
            n, e = _lift_edges(b, N, T, S)
            consider(n, e)
            budget = BUDGET_START
        else:
            budget = min(BUDGET_CAP, budget * 1.05)

    if not lib.is_valid(state["n"], state["e"], d, D):
        return 1, []
    return state["n"], state["e"]
