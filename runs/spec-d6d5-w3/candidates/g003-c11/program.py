import math
import random
import time

import lib

_BIG = 1000


def _unreached(N, adj, D, reps):
    """Total number of (representative, vertex) pairs not reached within distance D."""
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _lift_adj(k, G, mul, layers):
    """Bi-Cayley lift: A_{i,g} ~ B_{perm[i], mul(g, volt[i])} for every layer."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    seen = set()
    dup = 0
    for perm, volt in layers:
        for i in range(k):
            j = perm[i]
            s = volt[i]
            for g in range(G):
                a = i * G + g
                b = (k + j) * G + mul(g, s)
                key = (a, b)
                if key in seen:
                    dup += 1
                    continue
                seen.add(key)
                adj[a].append(b)
                adj[b].append(a)
    return N, adj, seen, dup


def _lift_cost(k, G, D, mul, layers):
    N, adj, _, dup = _lift_adj(k, G, mul, layers)
    # Left translations are automorphisms, so one representative per side suffices.
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    return _unreached(N, adj, D, reps) + _BIG * dup


def _anneal(d, k, G, D, mul, rng, deadline, iters):
    """Anneal voltages and per-layer target permutations; returns layers when cost is zero."""
    layers = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        volt = [rng.randrange(G) for _ in range(k)]
        layers.append([perm, volt])
    cost = _lift_cost(k, G, D, mul, layers)
    T = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.2, T * 0.997)
        lay = layers[rng.randrange(d)]
        old_p, old_v = lay[0][:], lay[1][:]
        if k >= 2 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            lay[0][i1], lay[0][i2] = lay[0][i2], lay[0][i1]
        else:
            lay[1][rng.randrange(k)] = rng.randrange(G)
        c2 = _lift_cost(k, G, D, mul, layers)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            lay[0][:] = old_p
            lay[1][:] = old_v
    return layers if cost == 0 else None


def _lift_edges(k, G, mul, layers):
    N, _, seen, _ = _lift_adj(k, G, mul, layers)
    return N, sorted(seen)


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G; returns (order, mul) or None."""
    divs = [k2 for k2 in range(1, G + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs[:6]:
        m = G // k2
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0)
    best_n = n0
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= target:
        return best

    if D >= 3:
        # Projective plane incidence graph (degree q+1 <= d, diameter 3).
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n2, e2 = lib.projective_plane_incidence(q)
                consider(n2, e2)
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n3, e3 = lib.araujo_lopez_graph(d - 2)
                consider(n3, e3)
            except Exception:
                pass

    # Main search for D >= 3: annealed bi-Cayley lifts over semidirect products,
    # with per-representative BFS cost and a climbing order target.
    if D >= 3 and d >= 3:
        while time.monotonic() < deadline and best_n < target:
            k = rng.choice([1, 2, 2, 3, 4])
            base = best_n // (2 * k)
            G = base + 1 + rng.randrange(max(3, base // 6))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            iters = 1200 if k == 1 else 700
            layers = _anneal(d, k, order, D, mul, rng, deadline, iters)
            if layers is not None:
                n, e = _lift_edges(k, order, mul, layers)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
