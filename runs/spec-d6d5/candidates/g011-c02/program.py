import math
import random
import time

import lib


_BIG = 10 ** 9


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    for _ in range(60):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [x for x in range(1, m)
                     if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        if order != G:
            continue
        return order, mul
    return None


class _Lift:
    """Bi-Cayley lift with kA A-vertices, kB B-vertices, and a variable dart multiset.

    Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
    Vertex A_i,g = i*G + g and B_j,h = (kA + j)*G + h.
    Left translation by any group element is an automorphism, so one representative
    per base vertex (the identity of its fibre) suffices for the diameter check.
    """

    def __init__(self, kA, kB, G, mul, D):
        self.kA, self.kB, self.G, self.mul, self.D = kA, kB, G, mul, D
        self._pc = {}

    def perm(self, s):
        p = self._pc.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.G)]
            self._pc[s] = p
        return p

    def cost(self, darts, limit):
        """Number of (representative, vertex) pairs at distance > D; exact if <= limit."""
        kA, kB, G, D = self.kA, self.kB, self.G, self.D
        N = (kA + kB) * G
        adj = [[] for _ in range(N)]
        for i, j, s in darts:
            pm = self.perm(s)
            ba = i * G
            bb = (kA + j) * G
            for g in range(G):
                a = ba + g
                b = bb + pm[g]
                adj[a].append(b)
                adj[b].append(a)
        reps = [i * G for i in range(kA)] + [(kA + j) * G for j in range(kB)]
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
                count += len(nxt)
                frontier = nxt
                if not frontier:
                    break
            total += N - count
            if total > limit:
                return total
        return total

    def edges(self, darts):
        kA, kB, G = self.kA, self.kB, self.G
        E = set()
        for i, j, s in darts:
            pm = self.perm(s)
            for g in range(G):
                E.add((i * G + g, (kA + j) * G + pm[g]))
        return (kA + kB) * G, sorted(E)


def _init_darts(kA, kB, d, G, rng):
    darts, keys = [], set()
    cA, cB = [0] * kA, [0] * kB
    target = min(kA, kB) * d
    tries = 0
    while len(darts) < target and tries < 2000:
        tries += 1
        i = rng.randrange(kA)
        j = rng.randrange(kB)
        if cA[i] >= d or cB[j] >= d:
            continue
        s = rng.randrange(G)
        if (i, j, s) in keys:
            continue
        darts.append([i, j, s])
        keys.add((i, j, s))
        cA[i] += 1
        cB[j] += 1
    return darts, keys, cA, cB


def _search(d, D, kA, kB, G, mul, rng, deadline, iters):
    """Annealing over voltages, endpoints, and the dart set (degree caps <= d)."""
    ctx = _Lift(kA, kB, G, mul, D)
    darts, keys, cA, cB = _init_darts(kA, kB, d, G, rng)
    cost = ctx.cost(darts, _BIG)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())
        r = rng.random()

        if r < 0.4 and darts:
            # Voltage change on one dart.
            idx = rng.randrange(len(darts))
            i, j, s = darts[idx]
            s2 = rng.randrange(G)
            if s2 == s or (i, j, s2) in keys:
                continue
            keys.discard((i, j, s))
            keys.add((i, j, s2))
            darts[idx][2] = s2
            c2 = ctx.cost(darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                keys.discard((i, j, s2))
                keys.add((i, j, s))
                darts[idx][2] = s

        elif r < 0.7 and darts:
            # Move one dart's B-endpoint.
            idx = rng.randrange(len(darts))
            i, j, s = darts[idx]
            j2 = rng.randrange(kB)
            if j2 == j or cB[j2] >= d or (i, j2, s) in keys:
                continue
            keys.discard((i, j, s))
            keys.add((i, j2, s))
            cB[j] -= 1
            cB[j2] += 1
            darts[idx][1] = j2
            c2 = ctx.cost(darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                keys.discard((i, j2, s))
                keys.add((i, j, s))
                cB[j2] -= 1
                cB[j] += 1
                darts[idx][1] = j

        elif r < 0.92:
            # Add a dart where both endpoints have spare capacity.
            i = rng.randrange(kA)
            j = rng.randrange(kB)
            if cA[i] >= d or cB[j] >= d:
                continue
            s = rng.randrange(G)
            if (i, j, s) in keys:
                continue
            darts.append([i, j, s])
            keys.add((i, j, s))
            cA[i] += 1
            cB[j] += 1
            c2 = ctx.cost(darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts.pop()
                keys.discard((i, j, s))
                cA[i] -= 1
                cB[j] -= 1

        else:
            # Remove a random dart.
            if not darts:
                continue
            idx = rng.randrange(len(darts))
            i, j, s = darts.pop(idx)
            keys.discard((i, j, s))
            cA[i] -= 1
            cB[j] -= 1
            c2 = ctx.cost(darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts.insert(idx, [i, j, s])
                keys.add((i, j, s))
                cA[i] += 1
                cB[j] += 1

    if cost == 0:
        return ctx.edges(darts), kA * G
    return None


def _saturate(n, edges, d, split, rng):
    """Add edges between deficient A-side (< split) and B-side (>= split) vertices."""
    E = list(edges)
    existing = set((min(u, v), max(u, v)) for u, v in E)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    L = [v for v in range(split) if deg[v] < d]
    R = [v for v in range(split, n) if deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (a, b) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main family: unbalanced, non-regular bi-Cayley lifts over semidirect products,
    # annealed with variable dart sets and degree caps, then saturated.
    while time.monotonic() < deadline:
        kA = rng.randint(1, 3)
        kB = rng.randint(1, 3)
        if kA + kB < 2:
            continue
        g_lo = best_n // (kA + kB) + 1
        G = rng.randint(g_lo, g_lo + max(2, g_lo // 20))
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        order, mul = grp
        run_deadline = min(deadline, time.monotonic() + 10.0)
        res = _search(d, D, kA, kB, order, mul, rng, run_deadline, 600)
        if res is None:
            continue
        (n, e), split = res
        e = _saturate(n, e, d, split, rng)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
