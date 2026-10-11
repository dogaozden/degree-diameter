import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (safe fallbacks): record AL graph, projective plane incidence,
# and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family A: bi-Cayley graphs over groups (unchanged from parent).
# a_x ~ b_{x s} for s in S, |S| = d, 1 in S, S S^-1 = G gives diameter 3.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by element v against S[j], j != skip."""
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
    """Find S of size d, containing the identity 0, with S S^-1 = G; None on failure or timeout."""
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
    """Candidate groups of order N: the cyclic group plus a sample of semidirect products Z_a x| Z_k."""
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
    """Multiplication table M and quotient table Q[x][y] = x * y^-1 for the group named by spec."""
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
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None."""
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


def _edges_from(N, d, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Family B (new, bold): unstructured two-sided covering annealing.
#
# For diameter 3 in a bipartite graph with all degrees <= d, it suffices that
# every two vertices on the SAME side share a common neighbour (cross pairs then
# are at distance <= 3 automatically, given no isolated vertices).
# So we look for a d-regular bipartite graph on N + N vertices in which every
# pair of A-vertices and every pair of B-vertices has a common neighbour.
#
# State: d-regular bipartite graph, nbA[a] / nbB[b] neighbour lists, and the
# common-neighbour counts cA, cB. Moves are double-edge swaps (preserving
# regularity and bipartiteness). Objective U = number of uncovered same-side
# pairs; annealing drives U to 0.
# ----------------------------------------------------------------------------

def _cover_anneal(N, d, rng, deadline):
    """Return the A-side neighbour lists of a valid regular cover graph on N+N vertices, or None."""
    nbA = [[(a + s) % N for s in range(d)] for a in range(N)]
    nbB = [[(b - s) % N for s in range(d)] for b in range(N)]
    adj = [bytearray(N) for _ in range(N)]
    for a in range(N):
        for b in nbA[a]:
            adj[a][b] = 1
    cA = [[0] * N for _ in range(N)]
    cB = [[0] * N for _ in range(N)]
    for b in range(N):
        L = nbB[b]
        for i in range(d):
            for j in range(d):
                if i != j:
                    cA[L[i]][L[j]] += 1
    for a in range(N):
        L = nbA[a]
        for i in range(d):
            for j in range(d):
                if i != j:
                    cB[L[i]][L[j]] += 1
    U = 0
    for x in range(N):
        for y in range(x + 1, N):
            if cA[x][y] == 0:
                U += 1
            if cB[x][y] == 0:
                U += 1

    def add_edge(a, b):
        nonlocal U
        rowA = cA[a]
        for y in nbB[b]:
            if rowA[y] == 0:
                U -= 1
            rowA[y] += 1
            cA[y][a] += 1
        rowB = cB[b]
        for z in nbA[a]:
            if rowB[z] == 0:
                U -= 1
            rowB[z] += 1
            cB[z][b] += 1
        nbB[b].append(a)
        nbA[a].append(b)
        adj[a][b] = 1

    def remove_edge(a, b):
        nonlocal U
        nbA[a].remove(b)
        nbB[b].remove(a)
        adj[a][b] = 0
        rowA = cA[a]
        for y in nbB[b]:
            rowA[y] -= 1
            cA[y][a] -= 1
            if rowA[y] == 0:
                U += 1
        rowB = cB[b]
        for z in nbA[a]:
            rowB[z] -= 1
            cB[z][b] -= 1
            if rowB[z] == 0:
                U += 1

    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-3)
    T0, T1 = 0.6, 0.02
    temp = T0
    it = 0
    while U > 0:
        it += 1
        if (it & 511) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            temp = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)
        a1 = rng.randrange(N)
        b1 = nbA[a1][rng.randrange(d)]
        a2 = rng.randrange(N)
        b2 = nbA[a2][rng.randrange(d)]
        if a1 == a2 or b1 == b2 or adj[a1][b2] or adj[a2][b1]:
            continue
        old = U
        remove_edge(a1, b1)
        remove_edge(a2, b2)
        add_edge(a1, b2)
        add_edge(a2, b1)
        delta = U - old
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            continue
        remove_edge(a1, b2)
        remove_edge(a2, b1)
        add_edge(a1, b1)
        add_edge(a2, b2)
    return nbA


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 5.0)
    if budget < 1.0:
        budget = 0.5 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        # Known record family for d = q + 2, q a prime power.
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
    except Exception:
        pass

    max_N = d * (d - 1) + 1  # hard cap for diameter 3 with max degree d

    # Phase 1: bi-Cayley search (structured), a bounded slice of the budget.
    try:
        phase1_deadline = start + 0.35 * budget
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < phase1_deadline:
            rem = phase1_deadline - time.monotonic()
            res = _search_N(N, d, rng, time.monotonic() + 0.7 * rem)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, d, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    # Phase 2 (bold): unstructured two-sided covering annealing, aiming above
    # the structured result. Only meaningful for diameter 3.
    try:
        if time.monotonic() < deadline:
            N = best[0] // 2 + 1
            while N <= max_N and N >= d and time.monotonic() < deadline:
                rem = deadline - time.monotonic()
                sub = time.monotonic() + 0.6 * rem
                nbA = _cover_anneal(N, d, rng, sub)
                if nbA is None:
                    break
                n = 2 * N
                e = [(a, N + b) for a in range(N) for b in nbA[a]]
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
