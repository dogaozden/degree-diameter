import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley graphs over (possibly non-abelian) groups.
#
# For a group G of order N and a k-subset S of G, let B(G,S) have parts
# A = {a_g} and B = {b_g}, with a_g ~ b_{g s} for s in S. It is k-regular,
# bipartite, has 2N vertices, and has diameter <= 3 exactly when S S^{-1} = G.
# Earlier versions only used cyclic G. Here G ranges over semidirect products
# Z_m x| Z_k, which include non-abelian groups, and we search S by annealing
# on the number of uncovered group elements.
# Fallbacks: incidence graph of PG(2,q) (diameter 3) and K_{d,d}.
# ----------------------------------------------------------------------------


def _tables(grp):
    """Return (N, M, I): multiplication table and inverse list for the group grp = (m, k, r)."""
    m, k, r = grp
    N, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return N, M, I


def _groups(N, rng):
    """Candidate groups of order N as (m, k, r) triples for semidirect_group, cyclic first."""
    out = []
    for m in range(N, 0, -1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 0))
            continue
        rs = [1]
        if k > 1:
            extra = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            rng.shuffle(extra)
            rs += extra[:2]
        for r in rs:
            out.append((m, k, r))
    return out[:6]


def _anneal(N, k, M, I, rng, deadline):
    """Find S subset of G (|S| = k) with S S^{-1} = G. Returns sorted S (element codes) or None."""
    if k > N or k < 2:
        return None
    S = rng.sample(range(N), k)
    inS = [False] * N
    for s in S:
        inS[s] = True
    # cnt[g] = number of ordered pairs (a, b), a != b in S, with a * b^{-1} = g.
    cnt = [0] * N
    for a in S:
        Ma = M[a]
        for b in S:
            if a != b:
                cnt[Ma[I[b]]] += 1
    unc = sum(1 for g in range(1, N) if cnt[g] == 0)
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(N)
        if inS[y]:
            continue
        others = S[:i] + S[i + 1:]
        Mx, Ix = M[x], I[x]
        My, Iy = M[y], I[y]
        delta = 0
        # Remove contributions of x.
        for s in others:
            g = Mx[I[s]]
            cnt[g] -= 1
            if cnt[g] == 0 and g:
                delta += 1
            g = M[s][Ix]
            cnt[g] -= 1
            if cnt[g] == 0 and g:
                delta += 1
        # Add contributions of y.
        for s in others:
            g = My[I[s]]
            if cnt[g] == 0 and g:
                delta -= 1
            cnt[g] += 1
            g = M[s][Iy]
            if cnt[g] == 0 and g:
                delta -= 1
            cnt[g] += 1
        T = 0.25 + 0.75 * math.exp(-(it % 200000) / 40000.0)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
            unc += delta
        else:
            # Undo the y additions, then the x removals.
            for s in others:
                cnt[My[I[s]]] -= 1
                cnt[M[s][Iy]] -= 1
            for s in others:
                cnt[Mx[I[s]]] += 1
                cnt[M[s][Ix]] += 1
    return sorted(S)


def _bicayley_graph(N, M, S):
    """Bi-Cayley graph: a_g (vertex g) ~ b_{g s} (vertex N + g*s) for s in S."""
    E = []
    for g in range(N):
        Mg = M[g]
        for s in S:
            E.append((g, N + Mg[s]))
    return 2 * N, E


def _group_search(k, deadline, rng):
    """Climb the group order N upward from near the Moore-type cap k^2-k+1; return best (n, E) or None."""
    Nmax = k * k - k + 1
    lo = max(k, int(0.8 * Nmax))
    best = None
    for N in range(lo, Nmax + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        end_N = now + (deadline - now) / (Nmax - N + 1)
        groups = _groups(N, rng)
        found = None
        for gi, grp in enumerate(groups):
            now = time.monotonic()
            if now >= end_N:
                break
            slot = (end_N - now) / (len(groups) - gi)
            NN, M, I = _tables(grp)
            S = _anneal(NN, k, M, I, rng, min(deadline, now + slot))
            if S is not None:
                found = (NN, M, S)
                break
        if found is not None:
            NN, M, S = found
            best = _bicayley_graph(NN, M, S)
    return best


def _pg_best(d):
    """Incidence graph of PG(2,q) for the largest prime power q <= d-1, q <= 23."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * float(time_limit), float(time_limit) - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for any D >= 2).
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3 and d >= 2 and time.monotonic() < deadline:
        rng = random.Random(seed * 1000003 + 31 * d + D)
        res = _group_search(d, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
