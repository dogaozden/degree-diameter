import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Base graphs and cover-based growth (diameter-preserving vertex additions).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within D-1; keeps diameter <= D."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices with the leftover spare degree (only shortens paths)."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: bitset distance oracle for bi-Cayley voltage lifts.
#
# The lift over G = Z_m x| Z_k2 has vertices A_{i,g} = i*G + g and
# B_{j,h} = (k+j)*G + h, with darts (i, j, s) joining A_{i,g} to B_{j, g*s}.
# Left multiplication by any group element is an automorphism that is
# transitive on each layer, so one representative per layer suffices.
# Each vertex's neighbourhood is stored as a Python int bitmask, and BFS
# advances whole frontiers with bit operations. This makes each cost
# evaluation several times cheaper than list-based BFS, so the annealer
# gets many more moves within the budget.
# ----------------------------------------------------------------------------

def _perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Unreached (representative, vertex) pairs within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    nb = [0] * N
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            nb[a] |= 1 << b
            nb[b] |= 1 << a
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        reach = 1 << src
        front = reach
        for _ in range(D):
            nxt = 0
            f = front
            while f:
                low = f & -f
                nxt |= nb[low.bit_length() - 1]
                f ^= low
            nxt &= ~reach
            if not nxt:
                break
            reach |= nxt
            front = nxt
        total += N - reach.bit_count()
    return total


def _lift_graph(e):
    k, G, mul, darts = e["k"], e["G"], e["mul"], e["darts"]
    E = set()
    for i, j, s in darts:
        pm = _perm(mul, G, s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G; falls back to cyclic Z_G."""
    for _ in range(40):
        k2 = rng.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    order, mul, _ = lib.semidirect_group(G, 1, 1)
    return order, mul


def _new_entry(d, ks, best_n, rng):
    """A random lift candidate whose order is just above the current best order."""
    k = rng.choice(ks)
    G = max(2, best_n // (2 * k) + 1 + rng.randrange(0, 3))
    order, mul = _group(G, rng)
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(order)])
    return {"k": k, "G": order, "mul": mul, "darts": darts, "cost": None}


def _anneal(d, D, e, rng, deadline, iters, T0):
    """Resumable simulated annealing on one lift candidate. Returns the cost reached."""
    k, G, mul, darts = e["k"], e["G"], e["mul"], e["darts"]
    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = e["cost"]
    if cost is None:
        cost = _cost(k, G, D, darts, perms)
    if cost == 0:
        e["cost"] = 0
        return 0
    T = T0
    decay = (0.2 / T0) ** (1.0 / max(1, iters))
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T *= decay
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    e["cost"] = cost
    return cost


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, degree d. It is Moore-optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    try:
        if D >= 3:
            bases = [b for b in (_best_pg(d), _araujo(d)) if b is not None]
            for b in bases:
                consider(b[0], b[1])
            if best_n < moore:
                for b in bases:
                    n2, e2 = _grow(b[0], b[1], d, D, start + 0.12 * time_limit, rng)
                    consider(n2, e2)

            # Successive-halving search over bi-Cayley lifts. Many cheap anneals run first,
            # and only the most promising candidates get long anneals.
            ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
            pool = []
            while time.monotonic() < deadline and best_n < moore:
                pool = [e for e in pool if 2 * e["k"] * e["G"] > best_n]
                while len(pool) < 8 and time.monotonic() < deadline:
                    e = _new_entry(d, ks, best_n, rng)
                    _anneal(d, D, e, rng, deadline, 250, 2.0)
                    pool.append(e)
                pool.sort(key=lambda x: x["cost"])
                pool = pool[:8]
                for e in pool[:2]:
                    if time.monotonic() >= deadline:
                        break
                    _anneal(d, D, e, rng, deadline, 1200, 1.0)
                    if e["cost"] == 0:
                        n, E = _lift_graph(e)
                        if consider(n, E):
                            pool = []
                            break
                if pool:
                    pool.sort(key=lambda x: x["cost"])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
