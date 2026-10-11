import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small (possibly non-abelian) groups.
#
# Let G be a group of order m and S a d-subset of G with identity in S.
# Join a_x ~ b_y iff x^{-1} y in S. The graph is d-regular and bipartite on 2m vertices.
#   a-a distance <= 2 iff S S^{-1} = G,
#   b-b distance <= 2 iff S^{-1} S = G,
#   a-b distance <= 3 follows from S S^{-1} S = G.
# So any such pair (G, S) gives diameter 3 and order 2m, with m <= d(d-1)+1.
# Cyclic Haar graphs are the special case G = Z_m. This search also uses
# semidirect products Z_a x|_r Z_b, which are non-abelian when r != 1.
# ----------------------------------------------------------------------------


def _specs(m):
    """Semidirect products Z_a x|_r Z_b with a*b = m, as (a, b, r). r = 1 gives the direct product."""
    out = []
    for a in range(1, m + 1):
        if m % a:
            continue
        b = m // a
        for r in range(1, max(a, 2)):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                out.append((a, b, r))
    return out


def _tables(spec):
    """Multiplication and inverse tables for the group named by spec. Identity is element 0."""
    a, b, r = spec
    order, mul, inv = lib.semidirect_group(a, b, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    INV = [inv(x) for x in range(order)]
    return M, INV


def _anneal(m, d, M, INV, rng, deadline, iters):
    """Anneal a d-subset S of G (identity included) with S S^{-1} = G and S^{-1} S = G. Returns S or None."""
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    A = [0] * m  # counts of ordered pairs (s, t) with s t^{-1} = g
    B = [0] * m  # counts of ordered pairs (s, t) with s^{-1} t = g

    def contrib(x, others):
        ix = INV[x]
        ca, cb = [], []
        for t in others:
            it = INV[t]
            ca.append(M[x][it])
            ca.append(M[t][ix])
            cb.append(M[ix][t])
            cb.append(M[it][x])
        return ca, cb

    zeros = 2 * (m - 1)  # uncovered non-identity elements across A and B
    for i in range(1, d):
        ca, cb = contrib(S[i], S[:i])
        for g in ca:
            if A[g] == 0:
                zeros -= 1
            A[g] += 1
        for g in cb:
            if B[g] == 0:
                zeros -= 1
            B[g] += 1

    exp = math.exp
    rand = rng.random
    for it in range(iters):
        if zeros == 0:
            return S
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        T = 0.8 * (0.05 / 0.8) ** (it / iters)
        idx = rng.randrange(1, d)
        old = S[idx]
        new = rng.randrange(1, m)
        if inS[new]:
            continue
        others = S[:idx] + S[idx + 1:]

        oa, ob = contrib(old, others)
        z = zeros
        for g in oa:
            A[g] -= 1
            if A[g] == 0:
                z += 1
        for g in ob:
            B[g] -= 1
            if B[g] == 0:
                z += 1

        na, nb = contrib(new, others)
        for g in na:
            if A[g] == 0:
                z -= 1
            A[g] += 1
        for g in nb:
            if B[g] == 0:
                z -= 1
            B[g] += 1

        delta = z - zeros
        if delta <= 0 or rand() < exp(-delta / T):
            zeros = z
            inS[old] = False
            inS[new] = True
            S[idx] = new
        else:
            for g in na:
                A[g] -= 1
            for g in nb:
                B[g] -= 1
            for g in oa:
                A[g] += 1
            for g in ob:
                B[g] += 1
    return S if zeros == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph.
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            try:
                consider(*lib.projective_plane_incidence(d - 1))
            except (ValueError, StopIteration, KeyError):
                pass
        # Araujo-Pardo & Lopez family when d-2 is a prime power.
        if best_n < lib.moore_bound(d, D) and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass

    if best_n >= lib.moore_bound(d, D):
        return best

    # Bold search: bi-Cayley graphs over semidirect products, diameter 3, order 2m.
    # Each success is a strict improvement because m starts at best_n // 2 + 1.
    if d >= 3:
        m_max = d * (d - 1) + 1
        m = max(d, best_n // 2 + 1)
        while m <= m_max and time.monotonic() < deadline:
            specs = _specs(m)
            rng.shuffle(specs)
            tables = {}
            iters = 40000
            found = False
            while not found and time.monotonic() < deadline:
                for spec in specs:
                    if time.monotonic() >= deadline:
                        break
                    if spec not in tables:
                        tables[spec] = _tables(spec)
                    M, INV = tables[spec]
                    S = _anneal(m, d, M, INV, rng, deadline, iters)
                    if S is not None:
                        edges = [(x, m + M[x][s]) for x in range(m) for s in S]
                        consider(2 * m, edges)
                        found = True
                        break
                iters = int(iters * 1.5)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
