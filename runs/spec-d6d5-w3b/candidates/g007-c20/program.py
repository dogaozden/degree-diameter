import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small shared helpers.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _adj_from(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _bad_pairs(n, edges, D):
    ball = _balls(n, _adj_from(n, edges), D)
    return sum(n - b.bit_count() for b in ball)


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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    return len(new), [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]


# ----------------------------------------------------------------------------
# Baseline families (small-D and calibration cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW helper: reach-gain greedy saturation.
#
# Adding only edges between deficient opposite-side vertices never breaks
# validity and never increases the vertex count, but the choice of pairs
# matters. Each pair (a, b) is scored by how many distance-<=D pairs it would
# create: vertices within D-1 of b that are not yet within D of a, and the
# symmetric term. Balls are recomputed in rounds, so scores are cheap and
# only slightly stale within a round.
# ----------------------------------------------------------------------------

def _greedy_saturate(n, edges, d, D, deadline, rng):
    edges = list(edges)
    adj = _adj_from(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        if not left or not right:
            break
        if len(left) * len(right) <= 3000:
            pairs = {(a, b) for a in left for b in right}
        else:
            pairs = {(rng.choice(left), rng.choice(right)) for _ in range(3000)}
        RD = _balls(n, adj, D)
        RD1 = _balls(n, adj, D - 1)
        scored = []
        for a, b in pairs:
            if (min(a, b), max(a, b)) in existing:
                continue
            s = (RD1[b] & ~RD[a]).bit_count() + (RD1[a] & ~RD[b]).bit_count()
            scored.append((s + 0.5 * rng.random(), a, b))
        if not scored:
            break
        scored.sort(reverse=True)
        quota = max(1, len(left) // 8)
        added = 0
        for _, a, b in scored:
            if added >= quota:
                break
            if deg[a] >= d or deg[b] >= d:
                continue
            key = (min(a, b), max(a, b))
            if key in existing:
                continue
            existing.add(key)
            edges.append((a, b))
            adj[a].append(b)
            adj[b].append(a)
            deg[a] += 1
            deg[b] += 1
            added += 1
        if added == 0:
            break
    return edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# The group acts regularly on each layer by left multiplication, so one
# representative per layer suffices for the distance cost.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices=None):
    choices = k2_choices or [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _anneal(d, D, k, G, mul, rng, deadline, iters, start_darts=None, T0=1.0):
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (edges_or_None, darts, cost). Metropolis acceptance is drawn up front.
    """
    if start_darts is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start_darts]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = _adj_from(cur_n, cur_e)
        ball = _balls(cur_n, adj, D)
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


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    """Build the full lift, delete far vertices, then fill spare degree greedily by reach gain."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _greedy_saturate(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Splice-and-switch growth from the best valid graph.
# ----------------------------------------------------------------------------

def _bad_pairs_fast(n, edges, D):
    return _bad_pairs(n, edges, D)


def _splice_pair(n, E, d, rng):
    """Insert a left vertex n and a right vertex n+1 of degree d by splicing d edges."""
    m = len(E)
    if m < d:
        return None
    x, y = n, n + 1
    used, xs, ys, chosen = set(), set(), set(), []
    tries = 0
    while len(chosen) < d and tries < 50000:
        tries += 1
        i = rng.randrange(m)
        if i in used:
            continue
        a, b = E[i]
        if b in xs or a in ys:
            continue
        used.add(i)
        xs.add(b)
        ys.add(a)
        chosen.append(i)
    if len(chosen) < d:
        return None
    newE = [E[i] for i in range(m) if i not in used]
    for i in chosen:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    return n + 2, newE


def _switch_anneal(n, E, D, deadline, rng, T0=2.0):
    """Anneal 2-switches to drive the bad-pair count to zero. Returns edges or None."""
    E = list(E)
    m = len(E)
    if m < 2:
        return None
    eset = set(E)
    cur = _bad_pairs_fast(n, E, D)
    best, best_E = cur, list(E)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.05, T0 * (1.0 - (now - start) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in eset or (c, b) in eset:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        new = _bad_pairs_fast(n, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cur = new
            if cur < best:
                best, best_E = cur, list(E)
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return best_E if best == 0 else None


def _splice_climb(n, E, d, D, deadline, rng, consider):
    cur_n, cur_E = n, E
    while time.monotonic() < deadline - 0.5:
        res = _splice_pair(cur_n, cur_E, d, rng)
        if res is None:
            break
        n2, E2 = res
        now = time.monotonic()
        att_end = min(deadline, now + max(2.0, (deadline - now) / 3.0))
        E3 = _switch_anneal(n2, E2, D, att_end, rng)
        if E3 is not None and consider(n2, E3):
            cur_n, cur_E = n2, E3


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Lift search: the main source of gains for D >= 5.
    if D >= 5 and d >= 3:
        loop_end = min(deadline, start + 0.8 * time_limit)
        ks = [1, 1, 1, 2, 2, 3, 4]
        k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        elite = {}
        while time.monotonic() < loop_end and best_n < moore:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            lo = max(2, base + 1)
            hi = lo + max(3, lo // 4 if k == 1 else lo // 8)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng, k2_pool) if rng.random() < 0.8 else None
            if g is None:
                g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            key = (k, order)

            start_darts, T0 = None, 1.0
            mul_use = mul
            if key in elite and rng.random() < 0.5:
                _, st, mul_use = elite[key]
                start_darts = _perturb(st, order, rng, rng.randint(1, 3))
                T0 = 0.5

            iters = 1500 if k == 1 else 400
            res, darts_out, c = _anneal(d, D, k, order, mul_use, rng, loop_end,
                                        iters, start_darts, T0)
            if res is not None:
                consider(res[0], res[1])
                continue

            if key not in elite or c < elite[key][0]:
                elite[key] = (c, darts_out, mul_use)

            # Near miss: repair by deletion, then greedy reach-gain saturation.
            if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < loop_end:
                rep_deadline = min(deadline, time.monotonic() + 4.0)
                out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
                if out is not None:
                    consider(out[0], out[1])

    # Splice-and-switch growth from the best valid graph found so far.
    if D >= 3 and d >= 3 and best_n < moore and time.monotonic() < deadline - 1.0:
        n0, e0 = best
        color0 = _bipartition(n0, _adj_from(n0, e0))
        E0 = [(u, v) if color0[u] == 0 else (v, u) for u, v in e0]
        _splice_climb(n0, E0, d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
