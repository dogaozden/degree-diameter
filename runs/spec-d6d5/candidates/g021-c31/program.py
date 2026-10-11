import math
import random
import time

import lib


_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


# ----------------------------------------------------------------------------
# Small algebraic fallbacks (valid for D = 3 and up).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Darts are grouped into d layers; layer L is a permutation of the k base
# vertices, so every base vertex has exactly d darts and the lift is d-regular.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
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
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _random_darts(d, k, G, rng):
    """d layers, each a random permutation of the k base vertices, with random voltages."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid.

    Returns early with a value > limit once the running total exceeds limit.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _local(d, D, k, G, mul, darts, perms, deadline, rng, sweeps):
    """Plateau-walking local search over voltages and layer endpoint swaps.

    Each dart move tries a few random voltages and keeps the best. Each swap exchanges
    the B-endpoints of two darts in one layer (layers stay permutations). Moves that
    do not increase cost are accepted; a small fraction of uphill moves are accepted
    too, so the walk can leave plateaus. Returns (best_cost, best_darts).
    """
    cost = _cost(k, G, D, darts, perms)
    best_c = cost
    best_d = [list(x) for x in darts]
    m = len(darts)
    for _ in range(sweeps):
        if best_c == 0 or time.monotonic() > deadline:
            break
        order_idx = list(range(m))
        rng.shuffle(order_idx)
        for idx in order_idx:
            if cost == 0 or time.monotonic() > deadline:
                break
            if rng.random() < 0.2 and k > 1:
                # Layer endpoint swap.
                L = idx // k
                a, b = rng.sample(range(k), 2)
                ia, ib = L * k + a, L * k + b
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                plateau = rng.random() < 0.02
                c2 = _cost(k, G, D, darts, perms, _BIG if plateau else cost)
                if c2 <= cost or plateau:
                    cost = c2
                else:
                    darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            else:
                # Voltage move: best of a few random voltages for this dart.
                old = darts[idx][2]
                oldp = perms[idx]
                bc, bs, bp = None, None, None
                for _ in range(6):
                    s = rng.randrange(G)
                    if s == old:
                        continue
                    darts[idx][2] = s
                    perms[idx] = _right_perm(mul, G, s)
                    c = _cost(k, G, D, darts, perms, bc if bc is not None else _BIG)
                    if bc is None or c < bc:
                        bc, bs, bp = c, s, perms[idx]
                darts[idx][2] = old
                perms[idx] = oldp
                if bs is None:
                    continue
                plateau = rng.random() < 0.02
                if bc <= cost or plateau:
                    darts[idx][2] = bs
                    perms[idx] = bp
                    cost = bc
            if cost < best_c:
                best_c = cost
                best_d = [list(x) for x in darts]
    return best_c, best_d


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion, then saturation with spare degree.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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
    return n, edges


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    """Build the full lift from darts, repair it, and saturate. Returns (n, edges) or None."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    return _saturate_edges(n, e, d, rng)


# ----------------------------------------------------------------------------
# Main search: for each sampled group, run a fresh local search from random darts.
# ----------------------------------------------------------------------------

def _search_lifts(d, D, deadline, rng, get_best_n, consider):
    while time.monotonic() < deadline:
        k = rng.choice([2, 2, 3, 3, 4])
        best_n = get_best_n()
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(2, lo // 10)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g

        darts = _random_darts(d, k, order, rng)
        perms = [_right_perm(mul, order, s) for _, _, s in darts]
        c, best_darts = _local(d, D, k, order, mul, darts, perms,
                               deadline, rng, sweeps=6)
        perms = [_right_perm(mul, order, s) for _, _, s in best_darts]

        if c == 0:
            n, e = _edges(k, order, best_darts, perms)
            consider(n, e)
            continue

        if c <= _REPAIR_MAX_COST and time.monotonic() < deadline:
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, mul, best_darts, rep_deadline, rng)
            if out is not None:
                consider(out[0], out[1])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 5:
        _search_lifts(d, D, deadline, rng, lambda: best_n, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
