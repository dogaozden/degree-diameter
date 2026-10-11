import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x| Z_k with element (a, b) coded as a*k + b.
# Identity is code 0.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k, r) with m*k = G, giving Z_m x| Z_k (r^k = 1 mod m), or None."""
    for _ in range(40):
        ks = [k for k in range(1, 13) if G % k == 0]
        k = rng.choice(ks)
        m = G // k
        if m < 2:
            continue
        if k == 1:
            r = 1
        else:
            cands = [x for x in range(1, m)
                     if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        return m, k, r
    return None


def _make_table(m, k, r):
    """Multiplication table T[x][y] and inverse list Ti[x] for the group (m, k, r)."""
    G = m * k
    pw = [pow(r, b, m) for b in range(k)]
    coords = [divmod(y, k) for y in range(G)]
    T = []
    for x in range(G):
        a, b = divmod(x, k)
        pb = pw[b]
        row = [((a + pb * c) % m) * k + (b + dd) % k for c, dd in coords]
        T.append(row)
    Ti = []
    for x in range(G):
        a, b = divmod(x, k)
        nb = (-b) % k
        Ti.append(((-pw[nb] * a) % m) * k + nb)
    return T, Ti


# ----------------------------------------------------------------------------
# Bi-Cayley graph B(G, S): A_g ~ B_{g s} for s in S (|S| = d).
# Left multiplication is an automorphism that is transitive on each side,
# so the diameter is at most D iff BFS from A_0 and from B_0 reaches everything
# within D steps.
# ----------------------------------------------------------------------------

def _cost(G, T, Ti, S, D):
    """Unreached (source, vertex) pairs from A_0 and B_0 within distance D."""
    N = 2 * G
    Sinv = [Ti[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = T[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - G]
                    for t in Sinv:
                        v = row[t]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _anneal(G, T, Ti, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S of size d. Returns S with cost 0, or None."""
    S = rng.sample(range(G), d)
    cost = _cost(G, T, Ti, S, D)
    temp = 2.0
    it = 0
    while cost > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(G, T, Ti, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[i] = old
        temp = max(0.3, temp * 0.995)
    return S if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Projective plane incidence graph: diameter 3, degree q + 1 <= d.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    if best_n >= lib._moore_bound(d, D):
        return best

    if D >= 3:
        # Bi-Cayley search: groups just above half the current best order.
        while time.monotonic() < deadline:
            lo = best_n // 2 + 1
            G = rng.randint(lo, lo + max(3, lo // 25))
            if G < d:
                continue
            g = _sample_group(G, rng)
            if g is None:
                continue
            m, k, r = g
            T, Ti = _make_table(m, k, r)
            S = _anneal(G, T, Ti, d, D, rng, deadline, 800)
            if S is not None:
                E = [(x, G + T[x][s]) for x in range(G) for s in S]
                consider(2 * G, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
