import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe bases: projective plane incidence graphs and K_{d,d}.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers used by the cover-based growth step.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given as adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidates using their radius balls; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best_i, best_g = -1, 0
        for idx, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best_g:
                best_i, best_g = idx, g
        if best_i < 0:
            break
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within D-1; every distance stays <= D."""
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
            for attempt in range(20):
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
    """Join deficient opposite-side vertices with spare degree. Adding edges never breaks validity."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover-vertex extension and edge saturation until neither helps."""
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
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
# New family: voltage lifts over a WIDER set of groups than before.
# Parent used only Z_m x| Z_k. Here we also sample direct products Z_m x Z_k
# and dihedral groups D_n, which gives a different landscape of lifts.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, mul(g,s)} for every g.
# Each round of the base graph is a permutation i -> j, so the lift is d-regular.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random group of order G from several families, or None."""
    for _ in range(60):
        kind = rng.choice(["sd", "dir", "dih"])
        if kind == "dih":
            if G % 2 or G < 6:
                continue
            n = G // 2

            def mul(x, y, n=n):
                a, s = divmod(x, 2)
                b, t = divmod(y, 2)
                return ((a + (b if s == 0 else -b)) % n) * 2 + ((s + t) & 1)

            return G, mul

        divs = [k for k in range(1, G + 1) if G % k == 0]
        k = rng.choice(divs)
        m = G // k
        if m < 2 and k < 2:
            continue
        if kind == "dir":
            if m < 1:
                continue

            def mul(x, y, m=m, k=k):
                a, b = divmod(x, k)
                c, e = divmod(y, k)
                return ((a + c) % m) * k + (b + e) % k

            return G, mul
        # kind == "sd": Z_m x| Z_k needs r with gcd(r, m) = 1 and r^k = 1 mod m.
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        order, mul2, _ = lib.semidirect_group(m, k, r)
        return order, mul2
    return None


def _cost(k, G, D, darts, perms):
    """Total number of ordered vertex pairs at distance > D in the lift. Zero means valid."""
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
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(N - x.bit_count() for x in reach)


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline):
    """Time-scheduled simulated annealing over voltages and round assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    start = time.monotonic()
    span = max(1e-6, deadline - start)
    T0, T1 = 3.0, 0.2
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        idx = rng.randrange(len(darts))
        if rng.random() < 0.6 or k == 1:
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new
            perms[idx] = [mul(g, new) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = old_pm
        else:
            L = idx // k
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    return _edges(k, G, darts, perms)


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

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
            gn, ge = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(gn, ge)
            if D == 3:
                # Calibration case: the projective-plane family is already the answer.
                if not lib.is_valid(best[0], best[1], d, D):
                    best = lib.haar_graph(d, range(d))
                return best

    if D >= 4:
        ks = [1, 2, 2, 3, 3, 4] if D >= 5 else [1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            now = time.monotonic()
            run_deadline = min(deadline, now + 8.0)
            res = _anneal(d, D, k, order, mul, rng, run_deadline)
            if res is not None:
                consider(res[0], res[1])
                gn, ge = _grow(res[0], res[1], d, D,
                               min(deadline, time.monotonic() + 3.0), rng)
                consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
