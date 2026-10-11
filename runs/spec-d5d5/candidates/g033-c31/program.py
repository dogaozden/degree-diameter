import math
import random
import time

import lib

ITERS = 450              # annealing steps per (group, connection sets) try
MAX_GROUPS = 40          # groups tried per attempt
BUDGET0 = 1.0            # initial seconds per attempt (grows geometrically)
PHASE_A_FRAC = 0.3       # share of the search time given to the one-orbit fallback


# ----------------------------------------------------------------------------
# Baseline families (fast, always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: two-orbit bi-Cayley (block-circulant) lifts.
#
# The parent uses one orbit per side: A_x -- B_{xs}, s in S, |S| = d.
# Here each side has k orbits, A_{i,x} (i < k) and B_{j,y} (j < k), x, y in G,
# where G = Z_m x| Z_k is a finite group of order N. The edges are
#     A_{i,x} -- B_{j, x s}   for s in S[i][j],
# so the block sizes form a degree pattern: every A-row and B-column sums to d.
# For k = 2 the only pattern with equal row and column sums is
#     [[a, d-a], [d-a, a]].
# Left multiplication by G is an automorphism, so the diameter check needs only
# BFS from A_{i,e} and B_{j,e}, which is 2k sources in total. Order is 2kN.
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


def _patterns(d, k):
    """Block-size matrices with all row and column sums equal to d."""
    if k == 1:
        return [[[d]]]
    return [[[a, d - a], [d - a, a]] for a in range(1, d // 2 + 1)]


def _unreached(N, k, T, invs, S, D):
    """Count (source, vertex) pairs at distance > D over the 2k orbit representatives."""
    kN = k * N
    V = 2 * kN
    Sinv = [[[invs[s] for s in S[i][j]] for i in range(k)] for j in range(k)]
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j in range(k):
                        base = kN + j * N
                        for s in S[i][j]:
                            v = base + row[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i in range(k):
                        base = i * N
                        for h in Sinv[j][i]:
                            v = base + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _anneal(N, k, T, invs, pat, rng, D, deadline):
    """Simulated annealing over the block elements to zero the unreached pairs."""
    S = [[rng.sample(range(N), pat[i][j]) for j in range(k)] for i in range(k)]
    cur = _unreached(N, k, T, invs, S, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / ITERS))
        i = rng.randrange(k)
        j = rng.randrange(k)
        block = S[i][j]
        c = rng.randrange(N)
        if c in block:
            continue
        pos = rng.randrange(len(block))
        old = block[pos]
        block[pos] = c
        v = _unreached(N, k, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            block[pos] = old
    return S if cur == 0 else None


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N until one gives a valid connection pattern, or time runs out."""
    pats = _patterns(d, k)
    if not pats:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        pat = rng.choice(pats)
        S = _anneal(N, k, T, invs, pat, rng, D, deadline)
        if S is not None:
            return T, S
    return None


def _edges(N, k, T, S):
    """Build the lifted graph: vertices A_{i,x} = i*N + x, B_{j,y} = k*N + j*N + y."""
    kN = k * N
    E = []
    for i in range(k):
        for j in range(k):
            for s in S[i][j]:
                for x in range(N):
                    E.append((i * N + x, kN + j * N + T[x][s]))
    return 2 * kN, E


def _search(k, d, D, lo, hi, deadline, rng, consider):
    """Ascending search over orders N in [lo, hi]; each success raises the floor."""
    budget = BUDGET0
    width = 2
    while lo <= hi and time.monotonic() < deadline:
        found = None
        for N in range(lo, min(hi, lo + width - 1) + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, k, d, D, rng, min(deadline, now + budget))
            if res is not None:
                found = (N, res)
                break
        if found is None:
            budget *= 1.5
            width = min(width + 1, 5)
        else:
            N, (T, S) = found
            n, e = _edges(N, k, T, S)
            consider(n, e)
            lo = N + 1
            budget = BUDGET0
            width = 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = min(0.85 * time_limit, time_limit - 3.0)
    deadline = start + max(total, 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Calibration-style case: incidence graph of PG(2, d-1) meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best[0], best[1]

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        consider(*lib.araujo_lopez_graph(d - 2))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    if d < 2 or D < 2:
        return best[0], best[1]

    moore = lib._moore_bound(d, D)

    # Phase A: one-orbit bi-Cayley lift near the record order (2N vertices).
    lo1 = max(d + 1, moore // 4 - 2)
    hi1 = moore // 4 + 2
    phase_a_end = start + PHASE_A_FRAC * (deadline - start)
    _search(1, d, D, lo1, hi1, phase_a_end, rng, consider)

    # Phase B: two-orbit lift (4N vertices), only orders that beat the current best.
    lo2 = max(d + 1, best[0] // 4 + 1)
    hi2 = moore // 4
    _search(2, d, D, lo2, hi2, deadline, rng, consider)

    return best[0], best[1]
