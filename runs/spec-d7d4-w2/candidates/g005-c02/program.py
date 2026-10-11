import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley construction (replaces the twin/cover growth of the parent).
#
# For a group G of order N and a set S of d distinct elements, let
#     A_x -- B_{x*s}   for x in G, s in S.
# Left multiplication by g is an automorphism, so G acts transitively on each
# side. Diameter <= D therefore reduces to checking the balls of radius D around
# A_e and B_e. Each candidate is scored by the number of vertices left uncovered,
# and simulated annealing moves one element of S at a time to drive that to 0.
# The search runs over several groups per order N (cyclic, direct product, and
# semidirect products Z_m x| Z_k), trying the largest N it can reach.
# ----------------------------------------------------------------------------

def _table(N, mul):
    """Multiplication table and inverses of a group on 0..N-1 whose identity is 0."""
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    inv = [row.index(0) for row in T]
    return T, inv


def _group_tables(N, rng):
    """A few non-isomorphic-looking groups of order N, as (T, inv) pairs."""
    out = [_table(N, lambda x, y: (x + y) % N)]  # cyclic

    divs = [a for a in range(2, N) if N % a == 0]
    dp = [a for a in divs if a * a <= N]
    if dp:  # direct product Z_a x Z_b, element i*b + j
        a = rng.choice(dp)
        b = N // a

        def dmul(x, y, a=a, b=b):
            return ((x // b + y // b) % a) * b + (x % b + y % b) % b

        out.append(_table(N, dmul))

    sd = []  # semidirect products Z_m x| Z_k
    for k in divs:
        m = N // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if rs:
            sd.append((m, k, rs))
    if sd:
        m, k, rs = rng.choice(sd)
        r = rng.choice(rs)
        _, mul, _ = lib.semidirect_group(m, k, r)
        out.append(_table(N, mul))
    return out


def _uncovered(T, inv, N, S, D):
    """Vertices not within distance D of A_e or of B_e (0 means diameter <= D)."""
    invS = [inv[s] for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = T[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = T[v - N]
                    for si in invS:
                        w = row[si]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += 2 * N - count
    return total


def _anneal(T, inv, N, d, D, rng, deadline):
    """Find S (|S| = d, distinct) with zero uncovered vertices, or return None."""
    if N == d:
        S = list(range(N))
        return S if _uncovered(T, inv, N, S, D) == 0 else None

    S = rng.sample(range(N), d)
    cost = _uncovered(T, inv, N, S, D)
    steps = 0
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        steps += 1
        if steps > 3000:  # random restart to escape a basin
            S = rng.sample(range(N), d)
            cost = _uncovered(T, inv, N, S, D)
            steps = 0
            continue
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _uncovered(T, inv, N, S2, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / 0.7):
            S, cost = S2, c2
    return S


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0)

    Nmax = lib.moore_bound(d, D) // 2  # per-side bound
    start = max(d, 2, (2 * Nmax) // 3)
    if Nmax < start:
        return best

    Ns = list(range(start, Nmax + 1))
    for idx, N in enumerate(Ns):
        now = time.monotonic()
        if now >= deadline:
            break
        share_n = max(0.2, (deadline - now) / (len(Ns) - idx))
        deadN = min(deadline, now + share_n)

        groups = _group_tables(N, rng)
        found = None
        for gi, (T, inv) in enumerate(groups):
            now = time.monotonic()
            if now >= deadN:
                break
            share = (deadN - now) / (len(groups) - gi)
            S = _anneal(T, inv, N, d, D, rng, now + share)
            if S is not None:
                found = (T, S)
                break

        if found is not None:
            T, S = found
            n = 2 * N
            edges = [(x, N + T[x][s]) for x in range(N) for s in S]
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)

    return best
