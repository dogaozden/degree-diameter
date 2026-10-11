import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baseline: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley (group voltage) search, rewritten as simulated annealing.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, with base sizes k.
# Each layer l is a permutation sigma_l of range(k); the dart (i, sigma_l(i), s)
# joins A_{i,g} to B_{sigma_l(i), g*s} for all g. Every A_i and every B_j then has
# degree exactly d, so the graph is d-regular and bipartite.
#
# Left multiplication by any h is an automorphism, so diameter <= D reduces to
# BFS of depth D from the 2k orbit representatives A_{i,0} and B_{j,0}.
# Cost = number of unreached (representative, vertex) pairs; zero means valid.
# ----------------------------------------------------------------------------

def _direct_table(a, b):
    """Multiplication table of Z_a x Z_b, element x*b + y, identity 0."""
    G = a * b
    return G, [[((g // b + h // b) % a) * b + ((g % b + h % b) % b) for h in range(G)]
               for g in range(G)]


def _sample_group(G, rng):
    """Return (G, mt) for a random group of order G: semidirect Z_m x| Z_k2, or Z_a x Z_b."""
    opts = [k2 for k2 in range(2, 13) if G % k2 == 0 and G // k2 >= 2]
    if opts and rng.random() < 0.7:
        k2 = rng.choice(opts)
        m = G // k2
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
            order, mul, _ = lib.semidirect_group(m, k2, r)
            return order, [[mul(g, h) for h in range(order)] for g in range(order)]
    divs = [a for a in range(2, G // 2 + 1) if G % a == 0]
    if divs and rng.random() < 0.5:
        a = rng.choice(divs)
        return _direct_table(a, G // a)
    return _direct_table(G, 1)  # cyclic


def _distinct(darts):
    return len({(x[0], x[1], x[2]) for x in darts}) == len(darts)


def _cost(k, G, mt, D, darts):
    """Number of unreached (representative, vertex) pairs within distance D."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + mt[g][s]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, darts, mt):
    E = []
    for i, j, s in darts:
        for g in range(G):
            E.append((i * G + g, (k + j) * G + mt[g][s]))
    return 2 * k * G, E


def _anneal(d, D, k, G, mt, rng, iters, deadline):
    """Simulated annealing over darts. Returns darts with zero cost, or None."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append([i, perm[i], rng.randrange(G)])
    tries = 0
    while not _distinct(darts) and tries < 1000:
        x = rng.choice(darts)
        x[2] = rng.randrange(G)
        tries += 1
    if not _distinct(darts):
        return None

    c = _cost(k, G, mt, D, darts)
    for it in range(iters):
        if c == 0:
            break
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        T = 1.0 * (1.0 - it / iters) + 0.05

        if k > 1 and rng.random() < 0.3:
            # Swap two B-targets inside one layer (keeps each layer a permutation).
            l = rng.randrange(d)
            a = l * k + rng.randrange(k)
            b = l * k + rng.randrange(k)
            if a == b:
                continue
            darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
            if not _distinct(darts):
                darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
                continue
            c2 = _cost(k, G, mt, D, darts)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
            else:
                darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
        else:
            # Change the group voltage of one dart.
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            if not _distinct(darts):
                darts[idx][2] = old
                continue
            c2 = _cost(k, G, mt, D, darts)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
            else:
                darts[idx][2] = old

    return darts if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
    except Exception:
        pass

    try:
        mb = lib._moore_bound(d, D)
    except Exception:
        mb = None

    try:
        while time.monotonic() < deadline:
            if mb is not None and best_n >= mb:
                break
            k = rng.choice([1, 1, 1, 2, 2, 3])
            G = best_n // (2 * k) + 1 + rng.randrange(0, 5)
            if G < 2:
                G = 2
            order, mt = _sample_group(G, rng)
            darts = _anneal(d, D, k, order, mt, rng, 2500, deadline)
            if darts is not None:
                n, e = _edges(k, order, darts, mt)
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
