import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

# One-orbit search (semidirect bi-Cayley graphs, 2N vertices).
MAX_GROUPS_PER_ATTEMPT = 12
ITERS = 600
T_HOT = 1.5
T_COLD = 0.15
WINDOW_FRAC = 0.95
BUDGET_START = 0.4
BUDGET_CAP = 3.0
ONE_ORBIT_SHARE = 0.35   # fraction of the usable time given to the one-orbit phase

# Two-orbit search (abelian lifts of a 2+2 base, 4G vertices). New in this version.
TWO_ITERS = 900
TWO_T_HOT = 2.0
TWO_T_COLD = 0.2
TWO_MAX_GROUPS = 6
TWO_WINDOW = 12
TWO_BUDGET_START = 1.0
TWO_BUDGET_CAP = 6.0


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# One-orbit search: bi-Cayley graphs over semidirect products Z_m x| Z_k.
# Vertices A_x and B_y (x, y in G); edge A_x -- B_{x s} for s in S, |S| = d.
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


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Annealing over S = {0, s_1, ..., s_{d-1}} to zero the unreached-pair count."""
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


def _attempt(N, d, D, rng, deadline):
    """Try semidirect groups of order N until a connection set with diameter <= D is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _one_orbit(d, D, rng, deadline, consider, best_n):
    """Window-focused search over one-orbit bi-Cayley graphs, until deadline."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        return
    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best_n // 2
    budget = BUDGET_START
    while time.monotonic() < deadline:
        lo = max(floor, bestN + 1)
        cands = list(range(lo, top + 1))
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            bestN = max(bestN, N)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1


# ----------------------------------------------------------------------------
# Two-orbit search (new): abelian lifts of a 2+2 base multigraph.
#
# Base: vertices A_0, A_1 (one side) and B_0, B_1 (other side). Between A_i and
# B_j put a set of voltages S[i][j] in G = Z_m x Z_k (abelian, with m | k so
# both cyclic and non-cyclic types appear). Lifted vertices are A_{i,x} and
# B_{j,y}, with edge A_{i,x} -- B_{j,x+g} for every g in S[i][j].
#
# Degree d needs |S00| + |S01| = d and |S10| + |S11| = d (A side), and
# |S00| + |S10| = d and |S01| + |S11| = d (B side). This is solved by
# |S00| = |S11| = p and |S01| = |S10| = d - p with 1 <= p <= d-1.
#
# Translations by G are automorphisms, so eccentricities of the four sources
# A_{0,0}, A_{1,0}, B_{0,0}, B_{1,0} decide the diameter. Order is 4G, which
# beats the one-orbit family when G is in the right range.
# ----------------------------------------------------------------------------

def _abelian_pairs(G):
    """All (m, k) with m * k = G and m | k, i.e. Z_m x Z_k in a canonical form."""
    out = []
    for m in range(1, G + 1):
        if G % m == 0:
            k = G // m
            if k % m == 0:
                out.append((m, k))
    return out


def _group_tables(m, k):
    """Addition table T[x][y] and negation table for Z_m x Z_k, element x = a*k + b."""
    G = m * k
    T = [[((x // k + y // k) % m) * k + ((x % k + y % k) % k) for y in range(G)]
         for x in range(G)]
    neg = [((-(x // k)) % m) * k + ((-(x % k)) % k) for x in range(G)]
    return T, neg


def _cost2(G, T, neg, S, D):
    """Total unreached (source, vertex) pairs for the four sources. Zero means diameter <= D."""
    Sn = [[[neg[g] for g in S[i][j]] for j in (0, 1)] for i in (0, 1)]
    G2 = 2 * G
    total = 0
    for src in (0, G, G2, G2 + G):
        seen = bytearray(4 * G)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < G2:
                    i = v // G
                    row = T[v - i * G]
                    for j in (0, 1):
                        base = G2 + j * G
                        for g in S[i][j]:
                            u = base + row[g]
                            if not seen[u]:
                                seen[u] = 1
                                nxt.append(u)
                else:
                    w = v - G2
                    j = w // G
                    row = T[w - j * G]
                    for i in (0, 1):
                        base = i * G
                        for h in Sn[i][j]:
                            u = base + row[h]
                            if not seen[u]:
                                seen[u] = 1
                                nxt.append(u)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 4 * G - count
    return total


def _anneal2(G, T, neg, d, D, p, rng, iters, deadline):
    """Annealing over the voltage sets with fixed block sizes to zero the cost."""
    sizes = [[p, d - p], [d - p, p]]
    S = [[rng.sample(range(G), sizes[i][j]) for j in (0, 1)] for i in (0, 1)]
    cur = _cost2(G, T, neg, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = TWO_T_HOT * (TWO_T_COLD / TWO_T_HOT) ** (it / iters)
        i = rng.randrange(2)
        j = rng.randrange(2)
        block = S[i][j]
        t = rng.randrange(len(block))
        c = rng.randrange(G)
        if c in block:
            continue
        old = block[t]
        block[t] = c
        v = _cost2(G, T, neg, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            block[t] = old
    return S if cur == 0 else None


def _attempt2(G, d, D, rng, deadline):
    """Try abelian groups of order G (cyclic and non-cyclic) until a valid base is found."""
    pairs = _abelian_pairs(G)
    rng.shuffle(pairs)
    for m, k in pairs[:TWO_MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, neg = _group_tables(m, k)
        p = rng.randint(1, d - 1)
        S = _anneal2(G, T, neg, d, D, p, rng, TWO_ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _edges2(G, T, S):
    """Edge list of the 4G-vertex two-orbit lift: A_i block 0..2G-1, B_j block 2G..4G-1."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            ba = i * G
            bb = 2 * G + j * G
            for g in S[i][j]:
                for x in range(G):
                    edges.append((ba + x, bb + T[x][g]))
    return edges


def _two_orbit(d, D, rng, deadline, consider, best_n):
    """Search for a two-orbit lift just above the current best order, until deadline."""
    Gmax = lib._moore_bound(d, D) // 4
    bestG = max(1, best_n // 4)   # need 4G > best_n
    budget = TWO_BUDGET_START
    while time.monotonic() < deadline:
        hi = min(Gmax, bestG + TWO_WINDOW)
        if hi <= bestG:
            break
        window = list(range(bestG + 1, hi + 1))
        rng.shuffle(window)
        success = False
        for G in window:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt2(G, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            consider(4 * G, _edges2(G, T, S))
            bestG = max(bestG, G)
            success = True
            break
        if not success:
            budget = min(TWO_BUDGET_CAP, budget * 1.5)


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = {"n": 1, "edges": []}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"] = n
            state["edges"] = e

    # Calibration: incidence graph of PG(2, d-1) meets the bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return state["n"], state["edges"]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d >= 2 and D >= 2:
        if d >= 3 and D >= 3:
            phase = start + ONE_ORBIT_SHARE * (deadline - start)
        else:
            phase = deadline
        _one_orbit(d, D, rng, phase, consider, state["n"])

    if d >= 3 and D >= 3 and time.monotonic() < deadline:
        _two_orbit(d, D, rng, deadline, consider, state["n"])

    n, e = state["n"], state["edges"]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
