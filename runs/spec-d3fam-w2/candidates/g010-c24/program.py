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
# Bi-Cayley graphs over (possibly non-abelian) groups: a_x ~ b_{x s}, s in S.
# Diameter 3 holds iff S S^-1 = G. Found by simulated annealing over S.
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
    """Candidate groups of order N: the cyclic group plus a sample of semidirect products."""
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
# NEW (bold) stage: degree-preserving local search directly on the bipartite
# incidence structure for diameter 3.
#
# For a bipartite graph with sides A, B, diameter <= 3 means:
#   * any two A-vertices share a neighbour (same-side distance must be 2),
#   * any two B-vertices share a neighbour,
#   * every A-B pair is joined by a path of length <= 3.
# We start from the best known graph, add one vertex to each side, and anneal
# over degree-preserving edge switches plus edge additions between deficient
# vertices, minimising the number of violated pairs. Success means a strictly
# larger valid graph; every result is re-checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _colors(n, edges):
    """Two-colouring of a bipartite graph, or None if it is not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _cost(nA, nB, mA, mB):
    """Number of violated pairs (same-side pairs without a common neighbour, plus cross pairs at distance > 3)."""
    fullA = (1 << nA) - 1
    fullB = (1 << nB) - 1
    same = 0
    cross = 0
    for a in range(nA):
        d2 = 0  # A-vertices at distance <= 2 from a (as a bitmask)
        m = mA[a]
        while m:
            low = m & -m
            d2 |= mB[low.bit_length() - 1]
            m ^= low
        r3 = 0  # B-vertices at distance <= 3 from a
        m = d2
        while m:
            low = m & -m
            r3 |= mA[low.bit_length() - 1]
            m ^= low
        same += (fullA & ~d2 & ~(1 << a)).bit_count()
        cross += (fullB & ~r3).bit_count()
    return same // 2 + cross


def _extend_sa(nA0, nB0, E0, d, rng, deadline):
    """Try to find a valid diameter-3 bipartite graph with one extra vertex per side, by annealing.

    Returns (nA, nB, edge_list) with edges as (a, b) index pairs, or None on failure or timeout.
    """
    nA = nA0 + 1
    nB = nB0 + 1
    mA = [0] * nA
    mB = [0] * nB
    dA = [0] * nA
    dB = [0] * nB
    E = []
    pos = {}

    def add(a, b):
        pos[a * nB + b] = len(E)
        E.append((a, b))
        mA[a] |= 1 << b
        mB[b] |= 1 << a
        dA[a] += 1
        dB[b] += 1

    def rem(a, b):
        i = pos.pop(a * nB + b)
        last = E.pop()
        if i < len(E):
            E[i] = last
            pos[last[0] * nB + last[1]] = i
        mA[a] &= ~(1 << b)
        mB[b] &= ~(1 << a)
        dA[a] -= 1
        dB[b] -= 1

    for a, b in E0:
        add(a, b)
    cost = _cost(nA, nB, mA, mB)
    T0 = 1.5
    t_start = time.monotonic()
    total = max(deadline - t_start, 1e-3)
    it = 0
    while cost > 0:
        if (it & 15) == 0 and time.monotonic() >= deadline:
            return None
        it += 1
        frac = (time.monotonic() - t_start) / total
        T = max(0.03, T0 * (1.0 - frac))
        defA = [a for a in range(nA) if dA[a] < d]
        defB = [b for b in range(nB) if dB[b] < d]
        if defA and defB and rng.random() < 0.4:
            a = rng.choice(defA)
            b = rng.choice(defB)
            if a * nB + b in pos:
                continue
            add(a, b)
            new = _cost(nA, nB, mA, mB)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                rem(a, b)
        else:
            if len(E) < 2:
                continue
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2:
                continue
            if (a1 * nB + b2) in pos or (a2 * nB + b1) in pos:
                continue
            rem(a1, b1)
            rem(a2, b2)
            add(a1, b2)
            add(a2, b1)
            new = _cost(nA, nB, mA, mB)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                rem(a1, b2)
                rem(a2, b1)
                add(a1, b1)
                add(a2, b2)
    return nA, nB, list(E)


def _bipartite_parts(n, edges, col):
    """Convert a 2-coloured graph into (nA, nB, [(a, b), ...]) with compact side indices."""
    idxA = {}
    idxB = {}
    for v in range(n):
        if col[v] == 0:
            idxA[v] = len(idxA)
        else:
            idxB[v] = len(idxB)
    E = []
    for u, v in edges:
        if col[u] == 0:
            E.append((idxA[u], idxB[v]))
        else:
            E.append((idxA[v], idxB[u]))
    return len(idxA), len(idxB), E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline_all = start + 0.85 * time_limit
    deadline_bc = start + 0.40 * time_limit
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

        # Bi-Cayley search over groups of order N, starting just above the current best.
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < deadline_bc:
            rem_t = deadline_bc - time.monotonic()
            budget = 0.7 * rem_t
            res = _search_N(N, d, rng, time.monotonic() + budget)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, d, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    # Bold stage: grow the best graph by one vertex per side via local search.
    try:
        if D == 3 and d >= 4 and best[0] < lib.moore_bound(d, D):
            col = _colors(best[0], best[1])
            if col is not None:
                nA0, nB0, E0 = _bipartite_parts(best[0], best[1], col)
                while time.monotonic() < deadline_all:
                    res = _extend_sa(nA0, nB0, E0, d, rng, deadline_all)
                    if res is None:
                        break
                    nA, nB, E = res
                    n = nA + nB
                    edges_out = [(a, nA + b) for a, b in E]
                    if n > best[0] and lib.is_valid(n, edges_out, d, D):
                        best = (n, edges_out)
                        nA0, nB0, E0 = nA, nB, E
                    else:
                        break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
