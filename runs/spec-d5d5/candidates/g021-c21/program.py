import math
import random
import time

import lib

MAX_GROUPS = 12          # groups tried per (N, k) attempt
PATTERNS_PER_GROUP = 3   # random degree patterns per group
ITERS = 2500             # annealing steps per try
KMAX = 4                 # maximum number of orbits per side
CAND_PER_K = 3           # candidate group orders per (k, tier)
TIERS = (0.46, 0.4935)   # order fractions of the Moore bound to target


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


def _pattern(k, d, rng):
    """Integer k x k matrix with all row and column sums d (sum of d random permutation matrices)."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            M[i][p[i]] += 1
    return M


def _unreached(N, k, T, invs, S, D):
    """Number of (source, vertex) pairs at distance > D, over one source per orbit on each side.

    Vertices: A_{i,x} = i*N + x, B_{j,y} = (k+j)*N + y.
    Edge A_{i,x} -- B_{j, x*g} for g in S[i][j]. Left multiplication is an automorphism,
    so one source per orbit suffices.
    """
    fwd = [[] for _ in range(k)]
    bwd = [[] for _ in range(k)]
    for i in range(k):
        for j in range(k):
            for g in S[i][j]:
                fwd[i].append((j, g))
                bwd[j].append((i, invs[g]))
    kN = k * N
    total = 2 * kN
    sources = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    tot = 0
    for src in sources:
        seen = bytearray(total)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in fwd[i]:
                        v = (k + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, gi in bwd[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        tot += total - count
    return tot


def _anneal(N, k, d, D, T, invs, pat, rng, iters, deadline):
    """Anneal the connection sets S[i][j] (distinct elements, |S[i][j]| = pat[i][j]) to zero bad pairs."""
    blocks = [(i, j, pat[i][j]) for i in range(k) for j in range(k) if pat[i][j] > 0]
    S = [[[] for _ in range(k)] for _ in range(k)]
    for i, j, c in blocks:
        S[i][j] = rng.sample(range(N), c)
    cur = _unreached(N, k, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.2, 2.0 * (1.0 - it / iters))
        i, j, c = blocks[rng.randrange(len(blocks))]
        slot = rng.randrange(c)
        new = rng.randrange(N)
        if new in S[i][j]:
            continue
        old = S[i][j][slot]
        S[i][j][slot] = new
        v = _unreached(N, k, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][slot] = old
    return S if cur == 0 else None


def _attempt(N, k, d, D, rng, deadline):
    """Search groups of order N and k orbits per side for a lift of diameter <= D."""
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        for _ in range(PATTERNS_PER_GROUP):
            if time.monotonic() > deadline:
                return None
            pat = _pattern(k, d, rng)
            S = _anneal(N, k, d, D, T, invs, pat, rng, ITERS, deadline)
            if S is not None:
                return T, S, k
    return None


def _make_edges(N, k, T, S):
    edges = []
    for i in range(k):
        for j in range(k):
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, (k + j) * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # K2 is always valid for d, D >= 1.
    consider(2, [(0, 1)])

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe fallbacks.
    if D >= 2 and d >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if q <= 12 and lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)

    # Candidate (k, N) pairs: total order n = 2*k*N near the targeted fractions of the Moore bound.
    cand_set = set()
    for frac in TIERS:
        lower = max(best_n + 1, int(frac * moore) + 1)
        for k in range(1, KMAX + 1):
            n0 = -(-lower // (2 * k))
            for N in range(max(n0, d), n0 + CAND_PER_K):
                if 2 * k * N <= moore:
                    cand_set.add((k, N))
    cands = sorted(cand_set, key=lambda c: 2 * c[0] * c[1])

    budget = 0.5
    while time.monotonic() < deadline:
        if all(2 * k * N <= best_n for k, N in cands):
            break
        for k, N in cands:
            if 2 * k * N <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, k, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S, kk = res
            consider(2 * kk * N, _make_edges(N, kk, T, S))
        budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
