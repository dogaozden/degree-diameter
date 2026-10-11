import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New main construction: Haar graphs H(G, S) over a finite group G of order N.
# Vertices a_g = g (side A) and b_h = N + h (side B); a_g ~ b_{g*s} for s in S.
# Left translations are automorphisms and act transitively on each side, so the
# diameter condition reduces to two BFS runs, from a_e and from b_e. Every
# Haar graph with |S| = d is d-regular and bipartite. We search for the largest
# order N whose Haar graph has diameter <= D. Cyclic groups use a bitmask BFS,
# which is very fast. Other groups use an explicit BFS.
# ----------------------------------------------------------------------------


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (only for small d)."""
    for q in range(min(d - 1, 25), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost_cyclic(N, S, D):
    """Uncovered (vertex, root) pairs from a_0 and b_0 in H(Z_N, S), via bitmask BFS."""
    full = (1 << N) - 1
    negs = [(N - s) % N for s in S]

    def nbr_b(X):
        # A-set X -> B-set {g + s}
        Y = 0
        for s in S:
            if s:
                Y |= ((X << s) | (X >> (N - s))) & full
            else:
                Y |= X
        return Y

    def nbr_a(Y):
        # B-set Y -> A-set {h - s}
        X = 0
        for s in negs:
            if s:
                X |= ((Y << s) | (Y >> (N - s))) & full
            else:
                X |= Y
        return X

    total = 0
    for root_side in (0, 1):
        if root_side == 0:
            rA, rB, f, side = 1, 0, 1, 0
        else:
            rA, rB, f, side = 0, 1, 1, 1
        for _ in range(D):
            if not f:
                break
            if side == 0:
                new = nbr_b(f) & ~rB
                rB |= new
            else:
                new = nbr_a(f) & ~rA
                rA |= new
            f = new
            side ^= 1
        total += 2 * N - rA.bit_count() - rB.bit_count()
    return total


def _cost_general(N, T, inv, S, D):
    """Uncovered pairs from a_e and b_e in H(G, S), with G given by its multiplication table T."""
    adj = [None] * (2 * N)
    for g in range(N):
        adj[g] = [N + T[g][s] for s in S]
    invS = [inv[s] for s in S]
    for h in range(N):
        adj[N + h] = [T[h][t] for t in invS]
    total = 0
    for src in (0, N):
        seen = [False] * (2 * N)
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - cnt
    return total


def _anneal(N, d, cost, rng, iters, deadline, lo):
    """Anneal a d-subset S of {0..N-1}. If lo == 1, element 0 is fixed in S (WLOG for cyclic groups)."""
    S = ([0] if lo else []) + rng.sample(range(lo, N), d - lo)
    c = cost(S)
    for it in range(iters):
        if c == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(lo, d)
        cand = rng.randrange(lo, N)
        if cand in S:
            continue
        old = S[i]
        S[i] = cand
        c2 = cost(S)
        temp = 1.5 * (0.02 ** (it / iters)) + 1e-9
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[i] = old
    return list(S) if c == 0 else None


def _abelian_mul(a, b):
    def mul(x, y):
        x1, y1 = divmod(x, b)
        x2, y2 = divmod(y, b)
        return ((x1 + x2) % a) * b + (y1 + y2) % b
    return mul


def _other_groups(N, rng, cap):
    """Non-cyclic groups of order N: semidirect products Z_m x| Z_k and non-cyclic abelian groups."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        for r in rng.sample(rs, min(len(rs), 2)):
            cands.append(lib.semidirect_group(m, k, r)[1])
    for a in range(2, N + 1):
        if a * a > N:
            break
        if N % a:
            continue
        b = N // a
        if math.gcd(a, b) == 1:
            continue  # cyclic, handled elsewhere
        cands.append(_abelian_mul(a, b))
    rng.shuffle(cands)
    return cands[:cap]


def _table(N, mul):
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _inverses(N, T):
    inv = [0] * N
    for x in range(N):
        row = T[x]
        for y in range(N):
            if row[y] == 0:  # identity is element 0 in every encoding used here
                inv[x] = y
                break
    return inv


def _haar_edges(N, S, op):
    return [(g, N + op(g, s)) for g in range(N) for s in S]


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best_n, best_e = 2 * d, lib.haar_graph(d, range(d))[1]
    ceiling = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or best_n >= ceiling:
        if not lib.is_valid(best_n, best_e, d, D):
            return 2 * d, lib.haar_graph(d, range(d))[1]
        return best_n, best_e

    # Ascending search over group orders N, Haar graph order 2N.
    N = max(d + 1, best_n // 2 + 1)
    while time.monotonic() < deadline and 2 * N <= ceiling:
        # Cyclic group: fast bitmask search.
        n_deadline = min(deadline, time.monotonic() + 2.0)
        S = _anneal(N, d, lambda S: _cost_cyclic(N, S, D), rng,
                    40000, n_deadline, 1)
        if S is not None:
            consider(2 * N, _haar_edges(N, S, lambda g, s: (g + s) % N))
        else:
            # Non-cyclic groups of the same order, explicit BFS.
            for mul in _other_groups(N, rng, 2):
                if time.monotonic() >= deadline:
                    break
                T = _table(N, mul)
                inv = _inverses(N, T)
                g_deadline = min(deadline, time.monotonic() + 0.7)
                S = _anneal(N, d, lambda S: _cost_general(N, T, inv, S, D),
                            rng, 8000, g_deadline, 0)
                if S is not None:
                    consider(2 * N, _haar_edges(N, S, lambda g, s: T[g][s]))
                    break
        N += 1

    if not lib.is_valid(best_n, best_e, d, D):
        return 2 * d, lib.haar_graph(d, range(d))[1]
    return best_n, best_e
