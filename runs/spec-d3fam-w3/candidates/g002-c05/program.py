import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Experimental: bi-Cayley graphs over NON-abelian groups.
#
# For a group G of order N and a d-subset S of G, the graph with vertices
# a_x, b_x (x in G) and edges a_x ~ b_{x s} (s in S) is d-regular and bipartite.
# Same-side pairs are at distance <= 2 iff S S^{-1} = G, and then every
# cross pair is at distance <= 3 (for g in G pick s3 in S; g s3^{-1} = s1 s2^{-1}).
# So the order is 2N with N <= d(d-1)+1. Abelian difference covers are one family;
# semidirect products Z_m x| Z_k give more group choices at the same order.
# ----------------------------------------------------------------------------


def _anneal(N, M, I, d, rng, deadline, iters):
    """Find a d-subset S of a group (mult table M, inverse table I) with S S^{-1} = G. Returns S or None."""
    S = rng.sample(range(N), d)
    inS = [False] * N
    for s in S:
        inS[s] = True
    cnt = [0] * N
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[M[S[i]][I[S[j]]]] += 1
    # Products s_i s_j^{-1} (i != j) never equal the identity, so cnt[0] stays 0.
    zeros = sum(1 for g in range(1, N) if cnt[g] == 0)
    exp = math.exp
    rand = rng.random

    for it in range(iters):
        if zeros == 0:
            return S
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        T = 0.8 * (0.02 / 0.8) ** (it / iters)
        idx = rng.randrange(d)
        old = S[idx]
        new = rng.randrange(N)
        if inS[new]:
            continue

        others = [S[j] for j in range(d) if j != idx]
        pold = []
        for t in others:
            pold.append(M[old][I[t]])
            pold.append(M[t][I[old]])
        z = zeros
        for x in pold:
            cnt[x] -= 1
            if cnt[x] == 0:
                z += 1

        S[idx] = new
        pnew = []
        for t in others:
            pnew.append(M[new][I[t]])
            pnew.append(M[t][I[new]])
        for x in pnew:
            if cnt[x] == 0:
                z -= 1
            cnt[x] += 1

        delta = z - zeros
        if delta <= 0 or rand() < exp(-delta / T):
            zeros = z
            inS[old] = False
            inS[new] = True
        else:
            for x in pnew:
                cnt[x] -= 1
            for x in pold:
                cnt[x] += 1
            S[idx] = old

    return S if zeros == 0 else None


def _group_specs(N, rng, limit):
    """Specs (m, k, r) of groups of order N: cyclic first, then random semidirect products Z_m x| Z_k."""
    out = [(N, 1, 1)]
    rest = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            rest.append((m, k, r))
    rng.shuffle(rest)
    out.extend(rest)
    return out[:limit]


def _make_group(N, spec):
    """Return (mul, M, I) for the group described by spec, or None if it cannot be built."""
    m, k, r = spec
    try:
        if k == 1:
            order, mul, inv = lib.cyclic_group(N)
        else:
            order, mul, inv = lib.semidirect_group(m, k, r)
    except (ValueError, ZeroDivisionError):
        return None
    if order != N:
        return None
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return mul, M, I


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        # Even cycle C_{2D}: bipartite, max degree 2, diameter D.
        if D >= 2:
            L = 2 * D
            consider(L, [(i, (i + 1) % L) for i in range(L)])
        return best

    if D == 2:
        return best

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph.
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family when d-2 is a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass

    # Bold search: bi-Cayley graphs over non-abelian groups of order N, one per N.
    # Ascending N from just above the current best half-order; each success is a strict improvement.
    if d >= 3:
        Nmax = d * (d - 1) + 1
        N0 = max(d, best_n // 2 + 1)
        group_cache = {}
        for N in range(N0, Nmax + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            remaining = deadline - now
            K = Nmax - N + 1
            nd = now + min(remaining, max(1.0, remaining / K * 1.5))

            specs = _group_specs(N, rng, 8)
            gi = 0
            found = False
            while time.monotonic() < nd and not found and specs:
                spec = specs[gi % len(specs)]
                gi += 1
                key = (N, spec)
                if key not in group_cache:
                    group_cache[key] = _make_group(N, spec)
                grp = group_cache[key]
                if grp is None:
                    if all(group_cache.get((N, s)) is None
                           for s in specs if (N, s) in group_cache) and gi > 4 * len(specs):
                        break
                    continue
                mul, M, I = grp
                S = _anneal(N, M, I, d, rng, nd, 60000)
                if S is not None:
                    n, e = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
                    consider(n, e)
                    found = True

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
