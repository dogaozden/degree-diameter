import itertools
import math
import random
import time

import lib

# New family used here: a two-orbit bi-Cayley graph (a 2x2 block voltage lift).
# Vertices are A^i_x and B^j_y for i, j in {0, 1} and x, y in G, with G a
# semidirect product Z_m x| Z_k of order N. For block (i, j) we choose a
# connection set S_ij of size c_ij, where c = [[a, d-a], [d-a, a]] so every
# vertex has degree d. Edges are A^i_x -- B^j_{x s} for s in S_ij. The order is
# 4N, which lets the search reach orders around 4 * 85 = 340, above the record 336.
# Left multiplication by G is an automorphism that fixes each orbit, so the
# diameter check only needs BFS from the four identity vertices.

MAX_GROUPS_PER_ATTEMPT = 12
ITERS = 800
T_HOT = 1.5
T_COLD = 0.15


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


def _lists(k, N, S, invs):
    """Neighbour rules per orbit: Aout[i] holds (B-offset, s); Bout[j] holds (A-offset, s^-1)."""
    Aout = [[] for _ in range(k)]
    Bout = [[] for _ in range(k)]
    for i in range(k):
        for j in range(k):
            for s in S[i][j]:
                Aout[i].append((k * N + j * N, s))
                Bout[j].append((i * N, invs[s]))
    return Aout, Bout


def _unreached(k, N, T, Aout, Bout, D):
    """Count (source, vertex) pairs not within distance D, over the 2k identity sources."""
    V = 2 * k * N
    kN = k * N
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for base, s in Aout[i]:
                        v = base + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for base, si in Bout[j]:
                        v = base + row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(k, N, T, invs, counts, D, rng, iters, deadline):
    """Anneal the connection sets S_ij to zero unreached pairs; return S or None."""
    blocks = [(i, j) for i in range(k) for j in range(k) if counts[i][j] > 0]
    S = [[None] * k for _ in range(k)]
    for i, j in blocks:
        S[i][j] = rng.sample(range(N), counts[i][j])

    def cost(SS):
        Aout, Bout = _lists(k, N, SS, invs)
        return _unreached(k, N, T, Aout, Bout, D)

    cur = cost(S)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(blocks)
        p = rng.randrange(len(S[i][j]))
        g = rng.randrange(N)
        if g in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = g
        v = cost(S)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N with random count matrices until one works or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        if k == 2:
            a = rng.randint(1, d - 1)
            counts = [[a, d - a], [d - a, a]]
        else:
            counts = [[d]]
        S = _anneal(k, N, T, invs, counts, D, rng, ITERS, deadline)
        if S is not None:
            return T, S, k
    return None


def _edges(k, N, T, S):
    """Return (n, edges) for the block bi-Cayley graph."""
    edges = []
    for i in range(k):
        for j in range(k):
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, k * N + j * N + T[x][s]))
    return 2 * k * N, edges


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
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

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    Nmax = moore // 4
    budget = 1.0
    while time.monotonic() < deadline:
        cands = [N for N in range(d + 1, Nmax + 1) if 4 * N > best_n]
        if not cands:
            break
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_dl = min(deadline, now + budget)
            res = _attempt(2, N, d, D, rng, att_dl)
            if res is None:
                continue
            T, S, k = res
            n, e = _edges(k, N, T, S)
            consider(n, e)
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
