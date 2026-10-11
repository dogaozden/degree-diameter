import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Finite groups as full multiplication tables.
# ----------------------------------------------------------------------------

def _finish_group(G, T):
    """Return (G, T, e) where e is the identity element of the table T."""
    ident = list(range(G))
    e = next((x for x in range(G) if T[x] == ident), 0)
    return G, T, e


def _affine_group(q):
    """Frobenius group AGL(1, q) of order q(q-1); element (a, b) is x -> a x + b, coded (a-1)*q + b."""
    F = lib.GF(q)
    T = [[0] * (q * (q - 1)) for _ in range(q * (q - 1))]
    for x in range(q * (q - 1)):
        a1, b1 = x // q + 1, x % q
        for y in range(q * (q - 1)):
            a2, b2 = y // q + 1, y % q
            a = F.mul(a1, a2)
            b = F.add(F.mul(a1, b2), b1)
            T[x][y] = (a - 1) * q + b
    return _finish_group(q * (q - 1), T)


def _sample_group(G, rng):
    """Random group of order G from several families (cyclic, semidirect, affine). Always returns one."""
    kinds = ["cyc"]
    for k2 in range(2, 13):
        if G % k2 == 0 and G // k2 >= 2:
            kinds.append(("sd", k2))
    q = next((q for q in range(2, G + 1)
              if q * (q - 1) == G and lib.is_prime_power(q)), None)
    if q is not None:
        kinds.append(("aff", q))
    choice = rng.choice(kinds)
    if choice == "cyc":
        return _finish_group(G, [[(x + y) % G for y in range(G)] for x in range(G)])
    if choice[0] == "aff":
        return _affine_group(choice[1])
    k2 = choice[1]
    m = G // k2
    cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not cands:
        return _finish_group(G, [[(x + y) % G for y in range(G)] for x in range(G)])
    r = rng.choice(cands)
    order, mulf, _ = lib.semidirect_group(m, k2, r)
    T = [[mulf(x, y) for y in range(order)] for x in range(order)]
    return _finish_group(order, T)


# ----------------------------------------------------------------------------
# Bi-Cayley graphs: k A-layers and k B-layers, each vertex of degree d.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g in G.
# Left multiplication is an automorphism, so one BFS per layer representative
# (at the identity) decides the diameter.
# ----------------------------------------------------------------------------

def _cost(k, G, e, T, D, darts):
    """Number of (representative, vertex) pairs unreached within D. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ai = i * G
        bj = (k + j) * G
        for g in range(G):
            a = ai + g
            b = bj + T[g][s]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G + e for i in range(k)] + [(k + j) * G + e for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, T, darts):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + T[g][s]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, e, T, rng, deadline, iters):
    """Simulated annealing over voltages and per-block target permutations."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, e, T, D, darts)
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / max(1, iters))
        idx = rng.randrange(len(darts))
        if k == 1 or rng.random() < 0.7:
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, e, T, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = idx // k
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, e, T, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, T, darts)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane meets the Moore bound when d-1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Main search: annealed bi-Cayley lifts over random groups of order just above
    # the current best per-layer size. Mostly k = 1 (Haar-type over non-abelian groups).
    ks = [1, 1, 1, 2, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        Gn, T, e = _sample_group(G, rng)
        res = _anneal(d, D, k, Gn, e, T, rng, deadline, 900)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
