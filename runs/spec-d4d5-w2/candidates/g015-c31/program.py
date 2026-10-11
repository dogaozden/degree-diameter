import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions (of time_limit). The Cayley stage runs first; the voltage-lift
# anneal uses the rest of the search budget; growth must finish by FRAC_TOTAL.
# ----------------------------------------------------------------------------
FRAC_LIFT = 0.68
FRAC_TOTAL = 0.90
CAYLEY_END = 0.45
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic base: projective plane incidence graph (D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: Cayley-bipartite search. A single A-layer and a single B-layer joined by
# d darts over a group Gamma: A_g ~ B_{g s} for s in S. Left multiplication is an
# automorphism, so diameter <= D is equivalent to every vertex of A_e and B_e
# reaching all 2|Gamma| vertices within D steps. The search anneals the set S
# (|S| = d) on the number of unreached (source, vertex) pairs, over many groups
# of each order, and pushes the order upward by one after each success.
# ----------------------------------------------------------------------------

def _group_specs(G, rng):
    """Shuffled list of (m, k2, r) with Z_m x|_r Z_k2 of order G (cyclic and abelian included)."""
    specs = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            specs.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                specs.append((m, k2, r))
    rng.shuffle(specs)
    return specs


def _group_tables(m, k2, r):
    """(order, multiplication table, inverse list) for the semidirect product."""
    order, mul, inv = lib.semidirect_group(m, k2, r)
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    it = [inv(x) for x in range(order)]
    return order, mt, it


def _unreached(S, Sinv, mt, G, D):
    """Number of (source, vertex) pairs at distance > D, sources A_e and B_e."""
    total = 0
    for src_a in (True, False):
        seen_a = bytearray(G)
        seen_b = bytearray(G)
        if src_a:
            seen_a[0] = 1
            fa, fb = [0], []
        else:
            seen_b[0] = 1
            fa, fb = [], [0]
        cnt = 1
        for step in range(D):
            if (step % 2 == 0) == src_a:
                nxt = []
                for g in fa:
                    row = mt[g]
                    for s in S:
                        h = row[s]
                        if not seen_b[h]:
                            seen_b[h] = 1
                            nxt.append(h)
                fb = nxt
            else:
                nxt = []
                for h in fb:
                    row = mt[h]
                    for si in Sinv:
                        g = row[si]
                        if not seen_a[g]:
                            seen_a[g] = 1
                            nxt.append(g)
                fa = nxt
            cnt += len(nxt)
            if cnt == 2 * G:
                break
        total += 2 * G - cnt
    return total


def _cayley_climb(mt, it, G, d, D, rng, deadline, iters):
    """Anneal a d-subset S of the group so that the Cayley bipartite graph has diameter <= D."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    cur = _unreached(S, [it[s] for s in S], mt, G, D)
    T = 2.0
    for step in range(iters):
        if cur == 0:
            return S
        if (step & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c = _unreached(T2, [it[s] for s in T2], mt, G, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = T2, c
        T = max(0.3, T * 0.999)
    return S if cur == 0 else None


def _cayley_stage(d, D, best_n, rng, deadline):
    """Find Cayley bipartite graphs of increasing order; returns the list of (n, edges) found."""
    moore = lib._moore_bound(d, D)
    hi = moore // 2
    lo = max(best_n // 2 + 1, (3 * hi) // 5)
    if lo > hi:
        lo = best_n // 2 + 1
    out = []
    while lo <= hi and time.monotonic() < deadline:
        G = lo + int((hi - lo) * rng.random() ** 2)
        found = None
        for (m, k2, r) in _group_specs(G, rng)[:4]:
            if time.monotonic() >= deadline:
                break
            order, mt, it = _group_tables(m, k2, r)
            for _ in range(2):
                now = time.monotonic()
                if now >= deadline:
                    break
                S = _cayley_climb(mt, it, order, d, D, rng,
                                  min(deadline, now + 2.0), 3000)
                if S is not None:
                    found = lib.group_lift(
                        2, [(0, 1, s) for s in S], order,
                        lambda x, g, mt=mt: mt[x][g])
                    break
            if found is not None:
                break
        if found is not None:
            out.append(found)
            lo = found[0] // 2 + 1
    return out


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
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


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            for attempt in range(200):
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _grow_best(n, edges, d, D, deadline, rng, tries=2):
    """Several randomized growth runs, keeping the largest result."""
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= deadline:
            break
        per = now + (deadline - now) / (tries - t)
        c = _grow(n, edges, d, D, per, rng)
        if c[0] > best[0]:
            best = c
    return best


def _swap_extend(n, edges, d, D, deadline, rng, max_fail=300):
    """Add cover vertices after random edge deletions; keep only valid steps."""
    if D < 2:
        return n, list(edges)
    cur_n = n
    cur_e = [tuple(e) for e in edges]
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        trial = list(cur_e)
        k_remove = rng.choice([0, 1, 1, 2, 3])
        for _ in range(min(k_remove, len(trial))):
            i = rng.randrange(len(trial))
            trial[i] = trial[-1]
            trial.pop()
        adj = [[] for _ in range(cur_n)]
        for u, v in trial:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        color = _bipartition(cur_n, adj)
        c = rng.randrange(2)
        cands = [s for s in range(cur_n) if color[s] == c and deg[s] < d]
        if not cands:
            fails += 1
            continue
        ball = _balls_radius(cur_n, adj, D - 1)
        chosen = _greedy_cover(cands, ball, (1 << cur_n) - 1, d, rng, True)
        if chosen is None:
            fails += 1
            continue
        v = cur_n
        new_e = trial + [(s, v) for s in chosen]
        new_n = cur_n + 1
        if lib.is_valid(new_n, new_e, d, D):
            cur_n, cur_e = new_n, new_e
            fails = 0
        else:
            fails += 1
    return cur_n, _saturate_edges(cur_n, cur_e, d, rng)


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2, annealed.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
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

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC_LIFT * time_limit
    final_deadline = start + FRAC_TOTAL * time_limit
    cayley_deadline = start + CAYLEY_END * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    pool = [fallback]
    moore = lib._moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            pool.append(best)
            pool.sort(key=lambda item: -item[0])
            del pool[4:]

    # Algebraic base for D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if pg[0] >= moore:
                return best
            consider(_grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng))

    # NEW: Cayley-bipartite search over all semidirect groups of each order.
    if best[0] < moore:
        try:
            for c in _cayley_stage(d, D, best[0], rng, cayley_deadline):
                consider(c)
        except Exception:
            pass

    # Main search: annealed group voltage lifts.
    try:
        if D >= 5:
            ks = [1, 1, 2, 2, 3, 4]
            anneal_iters = 1500
        else:
            ks = [1, 2, 2, 3, 4]
            anneal_iters = 400
        while time.monotonic() < deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            if D >= 5:
                G = max(2, base + 1 + rng.randrange(0, 3))
            else:
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, anneal_iters)
            if res is not None:
                consider(res)
    except Exception:
        pass

    # Final growth: for the top candidates, first cover-grow, then swap-extend.
    try:
        top = sorted(pool, key=lambda c: -c[0])[:3]
        for idx, c in enumerate(top):
            now = time.monotonic()
            if now >= final_deadline:
                break
            slice_end = now + (final_deadline - now) / (len(top) - idx)
            mid = now + 0.4 * (slice_end - now)
            grown = _grow_best(c[0], c[1], d, D, mid, rng, tries=2)
            consider(grown)
            sw = _swap_extend(grown[0], grown[1], d, D, slice_end, rng)
            consider(sw)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
