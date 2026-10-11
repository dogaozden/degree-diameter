import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# Baselines: K_{d,d} (diameter 2), the Araujo-Pardo & Lopez graph, and the
# projective plane incidence graph when they apply. These are always valid.
#
# Bold new family (D = 3 only): k-class bi-Cayley lifts over small groups.
#   - Vertices a^i_x and b^j_y for i, j in 0..k-1 and x, y in a group G of order N.
#   - For each class pair (i, j) choose a set S_ij of G with |S_ij| = C[i][j].
#     Row and column sums of C equal d, so every vertex has degree exactly d.
#   - Edge a^i_x ~ b^j_{x s} for s in S_ij. Left multiplication by G is an
#     automorphism, so it is transitive on each of the 2k classes. Diameter <= 3
#     therefore reduces to a BFS from one representative per class.
#   - Simulated annealing over the sets S_ij minimises the number of vertices
#     at distance > 3 from those 2k representatives.
#   - Groups are cyclic or semidirect products Z_a x| Z_k, chosen at random on
#     each restart. Order n = 2kN, so k = 2 and k = 3 are tried alongside k = 1.
#
# Every result is checked with lib.is_valid before it replaces the best graph,
# and the K_{d,d} fallback is always available.
# ----------------------------------------------------------------------------


def _baselines(d, D):
    """Best of K_{d,d}, the Araujo-Pardo & Lopez record, and PG(2,q) incidence."""
    best = lib.haar_graph(d, range(d))
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n_a, e_a = lib.araujo_lopez_graph(d - 2)
            if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                best = (n_a, e_a)
        except Exception:
            pass
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            try:
                n_p, e_p = lib.projective_plane_incidence(q)
                if n_p > best[0] and lib.is_valid(n_p, e_p, d, D):
                    best = (n_p, e_p)
            except Exception:
                pass
            break
    return best


def _group_specs(N):
    """Cyclic group plus every semidirect product Z_a x| Z_k of order N with a, k >= 2 (r ranges over 1..a-1)."""
    specs = [("cyc",)]
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                specs.append((a, k, r))
    return specs


def _table(spec, N):
    """Multiplication table M[x][y] = x*y and inverse list I for the group named by spec."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        _, mul, inv = lib.semidirect_group(*spec)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return M, I


def _sizes(k, d, rng):
    """k x k matrix of nonnegative integers with all row and column sums equal to d (sum of d random permutation matrices)."""
    C = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            C[i][p[i]] += 1
    return C


def _cost(S, N, k, M, I, D):
    """Total number of vertices at distance > D from the 2k class representatives (0 means diameter <= D)."""
    n = 2 * k * N
    total = 0
    for src in range(0, n, N):
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                t, x = divmod(v, N)
                if t < k:
                    # a^t_x is adjacent to b^j_{x s} for s in S[t][j]
                    Mx = M[x]
                    for j in range(k):
                        base = (k + j) * N
                        for s in S[t][j]:
                            u = base + Mx[s]
                            if not seen[u]:
                                seen[u] = 1
                                nxt.append(u)
                else:
                    # b^j_x is adjacent to a^i_{x s^-1} for s in S[i][j]
                    j = t - k
                    My = M[x]
                    for i in range(k):
                        base = i * N
                        for s in S[i][j]:
                            u = base + My[I[s]]
                            if not seen[u]:
                                seen[u] = 1
                                nxt.append(u)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - reached
    return total


def _run(N, k, M, I, C, D, rng, deadline):
    """One annealing run from a random start. Returns the sets S, or None if the deadline passes first."""
    S = [[rng.sample(range(N), C[i][j]) for j in range(k)] for i in range(k)]
    U = [[set(S[i][j]) for j in range(k)] for i in range(k)]
    pairs = [(i, j) for i in range(k) for j in range(k) if C[i][j] > 0]
    cost = _cost(S, N, k, M, I, D)
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 2.0 * (0.05 / 2.0) ** frac
        i, j = rng.choice(pairs)
        lst = S[i][j]
        idx = rng.randrange(len(lst))
        new = rng.randrange(N)
        if new in U[i][j]:
            continue
        old = lst[idx]
        lst[idx] = new
        U[i][j].discard(old)
        U[i][j].add(new)
        nc = _cost(S, N, k, M, I, D)
        delta = nc - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = nc
        else:
            lst[idx] = old
            U[i][j].discard(new)
            U[i][j].add(old)
    return S


def _attempt(N, k, d, D, rng, deadline):
    """Repeated annealing restarts (fresh group, sizes and sets) until success or deadline. Returns (S, M) or None."""
    specs = _group_specs(N)
    while time.monotonic() < deadline - 0.05:
        now = time.monotonic()
        run_end = min(deadline, now + max(2.0, (deadline - now) / 3))
        spec = rng.choice(specs)
        M, I = _table(spec, N)
        C = _sizes(k, d, rng)
        S = _run(N, k, M, I, C, D, rng, run_end)
        if S is not None:
            return S, M
    return None


def _edges(S, N, k, M):
    """Edges a^i_x -- b^j_{x s} for s in S[i][j]; vertex a^i_x = i*N + x, b^j_y = (k+j)*N + y."""
    E = []
    for i in range(k):
        for j in range(k):
            base_b = (k + j) * N
            for s in S[i][j]:
                for x in range(N):
                    E.append((i * N + x, base_b + M[x][s]))
    return E


def _search(d, D, best, rng, deadline):
    """Grow N for each class count k while annealing succeeds. Returns the best graph found."""
    moore = lib.moore_bound(d, D)
    for k in (2, 3, 1):
        N = max(d, best[0] // (2 * k) + 1)
        while 2 * k * N <= moore:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.5:
                return best
            budget = remaining * 0.5 if k != 1 else remaining
            res = _attempt(N, k, d, D, rng, now + budget)
            if res is None:
                break
            S, M = res
            n = 2 * k * N
            E = _edges(S, N, k, M)
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)
            N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = _baselines(d, D)

    if D != 3 or best[0] >= lib.moore_bound(d, D):
        return best

    try:
        cand = _search(d, D, best, rng, deadline)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
