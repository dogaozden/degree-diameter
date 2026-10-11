import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: Araujo-Pardo/Lopez record family, projective plane incidence,
# and K_{d,d} (diameter 2, valid for every D >= 2).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _baseline(d, D):
    best = lib.haar_graph(d, range(d))
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n_a, e_a = lib.araujo_lopez_graph(d - 2)
            if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                best = (n_a, e_a)
        except Exception:
            pass
    pg = _best_pg(d)
    if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
        best = pg
    return best


# ----------------------------------------------------------------------------
# Method A (new, non-Cayley): covering-design annealing for D = 3.
#
# Bipartite graph with parts A = {0..n-1} and B = {0..n-1}, both d-regular.
# For diameter 3 it suffices that every two A-vertices share a B-neighbour
# and every two B-vertices share an A-neighbour (same-side distance 2),
# and that cross pairs are within distance 3. The cross condition holds
# almost always for random-like d-regular graphs once the same-side
# condition holds, and it is verified with lib.is_valid anyway.
#
# State: adjacency lists and a pair-coverage count for each side.
# Move: edge swap (a1b1, a2b2) -> (a1b2, a2b1), which preserves degrees.
# Objective: number of uncovered same-side pairs (both sides together).
# ----------------------------------------------------------------------------

def _drop(lst, x, cov, n):
    """Remove x from lst, updating pair coverage; return change in uncovered pairs."""
    lst.remove(x)
    delta = 0
    for y in lst:
        i = x * n + y if x < y else y * n + x
        cov[i] -= 1
        if cov[i] == 0:
            delta += 1
    return delta


def _add(lst, x, cov, n):
    """Append x to lst, updating pair coverage; return change in uncovered pairs."""
    delta = 0
    for y in lst:
        i = x * n + y if x < y else y * n + x
        if cov[i] == 0:
            delta -= 1
        cov[i] += 1
    lst.append(x)
    return delta


def _move(a1, b1, a2, b2, adjA, adjB, covA, covB, n):
    """Replace edges a1-b1, a2-b2 by a1-b2, a2-b1; return change in uncovered pairs.

    Calling _move(a1, b2, a2, b1, ...) afterwards undoes the move exactly.
    """
    return (_drop(adjB[b1], a1, covA, n) + _add(adjB[b1], a2, covA, n)
            + _drop(adjB[b2], a2, covA, n) + _add(adjB[b2], a1, covA, n)
            + _drop(adjA[a1], b1, covB, n) + _add(adjA[a1], b2, covB, n)
            + _drop(adjA[a2], b2, covB, n) + _add(adjA[a2], b1, covB, n))


def _cover_sa(n, d, rng, deadline):
    """Find a d-regular bipartite graph on n+n vertices with all same-side pairs at distance 2.

    Returns adjA (list of B-neighbours for each A-vertex) or None on timeout.
    """
    if d > n:
        return None
    shifts = rng.sample(range(n), d)
    adjA = [[(a + s) % n for s in shifts] for a in range(n)]
    adjB = [[(b - s) % n for s in shifts] for b in range(n)]
    M = bytearray(n * n)
    for a in range(n):
        for b in adjA[a]:
            M[a * n + b] = 1
    covA = [0] * (n * n)
    covB = [0] * (n * n)
    for L, cov in ((adjB, covA), (adjA, covB)):
        for lst in L:
            for i in range(len(lst)):
                x = lst[i]
                for j in range(i + 1, len(lst)):
                    y = lst[j]
                    cov[x * n + y if x < y else y * n + x] += 1
    unc = 0
    for cov in (covA, covB):
        for x in range(n):
            base = x * n
            for y in range(x + 1, n):
                if cov[base + y] == 0:
                    unc += 1
    it = 0
    CYCLE = 200000
    while unc > 0:
        if (it & 1023) == 0 and time.monotonic() >= deadline:
            return None
        frac = (it % CYCLE) / CYCLE
        T = 0.8 * (0.02 ** frac) + 0.01
        it += 1
        a1 = rng.randrange(n)
        b1 = adjA[a1][rng.randrange(d)]
        a2 = rng.randrange(n)
        b2 = adjA[a2][rng.randrange(d)]
        if a1 == a2 or b1 == b2 or M[a1 * n + b2] or M[a2 * n + b1]:
            continue
        delta = _move(a1, b1, a2, b2, adjA, adjB, covA, covB, n)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            M[a1 * n + b1] = 0
            M[a2 * n + b2] = 0
            M[a1 * n + b2] = 1
            M[a2 * n + b1] = 1
            unc += delta
        else:
            _move(a1, b2, a2, b1, adjA, adjB, covA, covB, n)
    return adjA


def _edges_from_adjA(n, adjA):
    """Vertex a in A is a, vertex b in B is n + b."""
    return 2 * n, [(a, n + b) for a in range(n) for b in adjA[a]]


# ----------------------------------------------------------------------------
# Method B (kept from the parent): bi-Cayley graphs over small groups.
# a_x ~ b_{x s} for s in S, with S S^-1 = G giving diameter 3 on 2N vertices.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    change = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for y in (Q[v][b], Q[b][v]):
            if sign > 0:
                if cnt[y] == 0:
                    change -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    change += 1
    return change


def _anneal(N, d, Q, rng, deadline, moves):
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    unc = N - 1
    for j in range(d):
        for k in range(d):
            if j != k:
                y = Q[S[j]][S[k]]
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    if unc == 0:
        return S
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.5 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        delta = _delta(cnt, S, idx, old, -1, Q) + _delta(cnt, S, idx, x, 1, Q)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _delta(cnt, S, idx, x, -1, Q)
            _delta(cnt, S, idx, old, 1, Q)
    return None


def _specs(N, rng, cap=16):
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a == 1:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, Q


def _search_N(N, d, rng, deadline):
    specs = _specs(N, rng)
    cache = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in cache:
            try:
                cache[spec] = _tables(spec, N)
            except Exception:
                cache[spec] = None
        tab = cache[spec]
        if tab is None:
            continue
        M, Q = tab
        S = _anneal(N, d, Q, rng, deadline, 30000)
        if S is not None:
            return S, M
    return None


def _edges_bicayley(N, S, M):
    return [(x, N + M[x][s]) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    window = 0.8 * time_limit          # keep a margin under the limit
    deadline = start + window

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _baseline(d, D)
    if D < 3 or d < 3:
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    rng = random.Random(seed)
    try:
        # Phase A: covering-design annealing (non-Cayley), starting just above the record.
        deadline_a = start + 0.55 * window
        n = best[0] // 2 + 1
        while n - 1 <= d * (d - 1) and time.monotonic() < deadline_a:
            adj = _cover_sa(n, d, rng, deadline_a)
            if adj is None:
                break
            N, e = _edges_from_adjA(n, adj)
            if N > best[0] and lib.is_valid(N, e, d, D):
                best = (N, e)
                n += 1
            else:
                break

        # Phase B: bi-Cayley search over small groups, for the remaining time.
        N = best[0] // 2 + 1
        while N <= d * (d - 1) + 1 and time.monotonic() < deadline:
            res = _search_N(N, d, rng, deadline)
            if res is None:
                break
            S, M = res
            N2, e2 = 2 * N, _edges_bicayley(N, S, M)
            if N2 > best[0] and lib.is_valid(N2, e2, d, D):
                best = (N2, e2)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
