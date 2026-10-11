import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bipartite Cayley graphs over small non-abelian groups.
#
# Vertices are (g, 0) and (g, 1) for g in a group G of order N. For a connection
# set S of d distinct group elements, (g, 0) is joined to (g*s, 1) for s in S.
# Left multiplication is an automorphism, so the diameter test only needs BFS
# from (e,0) and (e,1). Simulated annealing over S minimizes the number of
# unreached vertices within distance D. Groups are semidirect products
# Z_m x| Z_k, which lib.semidirect_group provides.
# ----------------------------------------------------------------------------


def _groups_of_order(N):
    """Return (m, k, r) triples for Z_m x|_r Z_k of order N."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


def _tables(N, mul, inv):
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return T, I


def _cost(N, T, S, Sinv, D):
    """Number of (start, vertex) pairs unreached within D, summed over starts (e,0) and (e,1)."""
    V = 2 * N
    total = 0
    for start in (0, N):
        seen = [False] * V
        seen[start] = True
        frontier = [start]
        cnt = 1
        for _ in range(D):
            if not frontier:
                break
            nxt = []
            for v in frontier:
                if v < N:
                    row = T[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = True
                            nxt.append(w)
                else:
                    row = T[v - N]
                    for si in Sinv:
                        w = row[si]
                        if not seen[w]:
                            seen[w] = True
                            nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _search_group(N, T, I, d, D, rng, steps, deadline):
    """Anneal a connection set S of size d; return list S with zero cost, or None."""
    S = rng.sample(range(N), d)

    def cost_of(SS):
        return _cost(N, T, SS, [I[s] for s in SS], D)

    cur = cost_of(S)
    if cur == 0:
        return S
    for it in range(steps):
        if time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        old = S[i]
        S[i] = t
        new = cost_of(S)
        temp = max(0.05, 1.5 * (1.0 - it / steps))
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            if cur == 0:
                return list(S)
        else:
            S[i] = old
    return None


def _cayley_search(d, D, deadline, rng, best_n, consider):
    """Search increasing group orders N; call consider(n, edges) on each valid success."""
    Nmax = lib._moore_bound(d, D) // 2
    N = max(d, best_n // 2 + 1)
    fails = 0
    while N <= Nmax and time.monotonic() < deadline and fails < 4:
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        groups = groups[:12]
        if not groups:
            N += 1
            continue
        remaining = deadline - time.monotonic()
        n_deadline = time.monotonic() + max(1.0, min(remaining, 0.06 * (deadline - start_marker[0])))
        n_deadline = min(n_deadline, deadline)
        found = None
        for (m, k, r) in groups:
            if time.monotonic() > n_deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            if order != N:
                continue
            T, I = _tables(N, mul, inv)
            S = _search_group(N, T, I, d, D, rng, 350, n_deadline)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(g, N + T[g][s]) for g in range(N) for s in S]
            consider(2 * N, edges)
            fails = 0
        else:
            fails += 1
        N += 1


start_marker = [0.0]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    start_marker[0] = start
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3 seed: incidence graph of PG(2, q) with q + 1 <= d.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    if best[0] >= lib._moore_bound(d, D):
        return best

    if d >= 2 and time.monotonic() < deadline:
        _cayley_search(d, D, deadline, rng, best[0], consider)

    return best
