import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Shared graph helpers.
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


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _adj_of(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


# ----------------------------------------------------------------------------
# Projective-plane baselines (D = 3 and small D).
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
# NEW: degree-preserving switch repair.
#
# Take a d-regular bipartite graph whose diameter is slightly too large and
# repair it by bipartite 2-switches: (a,b),(c,e) -> (a,e),(c,b), with a,c on
# side 0 and b,e on side 1. Every switch keeps all degrees, keeps the graph
# bipartite and simple, so the vertex count is unchanged. Annealed on the
# number of bad pairs. Used on near-miss voltage lifts whose order already
# beats the best graph found so far.
# ----------------------------------------------------------------------------

def _switch_repair(n, E, D, deadline, rng):
    """Return (n, edges) with diameter <= D, or None if the deadline passes first.

    E holds (a, b) pairs with a on side 0 and b on side 1.
    """
    E = [[a, b] for a, b in E]
    m = len(E)
    if m < 2:
        return None
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    cost = _bad_pairs(n, adj, D)
    T = 1.0
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        # Rejects a == c and b == e automatically, since those would trip these checks.
        if e in adj[a] or b in adj[c]:
            continue
        # Apply: remove (a,b),(c,e); add (a,e),(c,b).
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            # Revert.
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
        T = max(0.05, T * 0.999)
    return n, [(a, b) for a, b in E]


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, mul(g, s)} for all g.
# The group acts on each layer by left multiplication, so one representative
# per layer suffices for the diameter check.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_SWITCH_MAX_BAD = 30


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
    return [mul(g, s) for g in range(G)]


def _quotient_cost(k, G, darts, perms, limit):
    """Number of (representative, vertex) pairs unreached within D. Zero means valid.

    Stops early once the running total exceeds `limit`.
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
    return reps, adj, N


def _cost_fn(k, G, D, darts, perms, limit):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    reps, adj, N = _quotient_cost(k, G, darts, perms, limit)
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


def _lift_edges(k, G, darts, mul):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + mul(g, s)))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        out[rng.randrange(len(out))][2] = rng.randrange(G)
    return out


def _anneal(d, D, k, G, mul, rng, deadline, iters, darts):
    """Anneal voltages and B-assignments. Returns (cost, darts)."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_fn(k, G, D, darts, perms, _BIG)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            old_p = perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost_fn(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_fn(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost, darts


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D >= 4:
        ks = [1, 1, 1, 2, 2, 3]
        elite = {}  # (k, order) -> (cost, darts)
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            lo = best_n // (2 * k) + 1
            hi = lo + max(2, lo // 6)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            key = (k, order)

            if key in elite and rng.random() < 0.5:
                darts = _perturb(elite[key][1], order, rng, rng.randint(1, 3))
            else:
                darts = _random_darts(d, k, order, rng)

            iters = 1500 if k == 1 else 400
            c, darts = _anneal(d, D, k, order, mul, rng, deadline, iters, darts)
            n_full, E = _lift_edges(k, order, darts, mul)

            if c == 0:
                consider(n_full, E)
                continue

            if key not in elite or c < elite[key][0]:
                elite[key] = (c, [list(x) for x in darts])

            # NEW: switch repair on a near-miss lift that is larger than the record so far.
            if n_full > best_n and time.monotonic() < deadline:
                adj = _adj_of(n_full, E)
                if _bad_pairs(n_full, adj, D) <= _SWITCH_MAX_BAD:
                    sr_deadline = min(deadline, time.monotonic() + 10.0)
                    out = _switch_repair(n_full, E, D, sr_deadline, rng)
                    if out is not None:
                        consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
