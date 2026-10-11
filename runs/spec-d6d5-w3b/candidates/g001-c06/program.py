import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small graph utilities (bitmask balls, bipartition, adjacency).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _adj(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _balls(n, adj, r):
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


def _bad(n, E, D):
    """Ordered count of (vertex, vertex) pairs at distance more than D."""
    adj = _adj(n, E)
    return sum(n - b.bit_count() for b in _balls(n, adj, D))


def _color(n, adj):
    c = [-1] * n
    for s in range(n):
        if c[s] != -1:
            continue
        c[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if c[v] == -1:
                    c[v] = 1 - c[u]
                    st.append(v)
    return c


# ----------------------------------------------------------------------------
# Base families.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    E = []
    nl = 0
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            for p in L:
                E.append((p, P + nl))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return 2 * P, E


# ----------------------------------------------------------------------------
# Greedy cover extension and saturation (only adds vertices / edges).
# ----------------------------------------------------------------------------

def _grow(n, E, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within D-1, then saturate."""
    E = list(E)
    adj = _adj(n, E)
    deg = [len(a) for a in adj]
    col = _color(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            pool = [s for s in range(n) if col[s] == c and deg[s] < d]
            rng.shuffle(pool)
            chosen, cov = [], 0
            while cov != full and len(chosen) < d and pool:
                bi = max(range(len(pool)), key=lambda i: (ball[pool[i]] & ~cov).bit_count())
                s = pool.pop(bi)
                if (ball[s] & ~cov) == 0:
                    break
                chosen.append(s)
                cov |= ball[s]
            if cov == full and chosen:
                v = n
                n += 1
                col.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    E.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return _saturate(n, E, d, rng)


def _saturate(n, E, d, rng):
    E = list(E)
    adj = _adj(n, E)
    deg = [len(a) for a in adj]
    col = _color(n, adj)
    ex = {(min(u, v), max(u, v)) for u, v in E}
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, E


def _repair(n, E, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, E) or None."""
    while time.monotonic() < deadline:
        if n == 0:
            return None
        adj = _adj(n, E)
        ball = _balls(n, adj, D)
        bad = [n - b.bit_count() for b in ball]
        if not any(bad):
            return n, E
        bv = [v for v in range(n) if bad[v] > 0]
        rng.shuffle(bv)
        bv.sort(key=lambda v: -bad[v])
        dead = set(bv[:max(1, len(bv) // 12)])
        keep = sorted(v for v in range(n) if v not in dead)
        new = {v: i for i, v in enumerate(keep)}
        E = [(new[u], new[v]) for u, v in E if u in new and v in new]
        n = len(keep)
    return None


# ----------------------------------------------------------------------------
# NEW: signed double cover annealing.
#
# Each base edge (u, v) gets a Z_2 voltage s. The cover has 2n vertices u and
# u+n, with edges (u, v+s*n) and (u+n, v+(1-s)*n). Degrees are preserved and
# the cover is bipartite (every cover edge joins base-opposite colour classes).
# Simulated annealing on sign flips drives the bad-pair count of the cover to
# zero, which doubles the order of a valid graph whenever such signs exist.
# ----------------------------------------------------------------------------

def _signed_cover(n, E, D, deadline, rng):
    m = len(E)
    if m == 0:
        return None
    sg = [rng.randrange(2) for _ in range(m)]

    def build_cover(sg):
        C = []
        for (u, v), s in zip(E, sg):
            C.append((u, v + s * n))
            C.append((u + n, v + (1 - s) * n))
        return C

    cur = _bad(2 * n, build_cover(sg), D)
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(m)
        sg[i] ^= 1
        c2 = _bad(2 * n, build_cover(sg), D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            sg[i] ^= 1
        T = max(0.2, T * 0.999)
    return build_cover(sg) if cur == 0 else None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k2 (annealed).
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for all g.
# Left multiplication is an automorphism, so only block representatives matter.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    ks = [1, 2, 3, 4, 6, 8, 12]
    for _ in range(60):
        k2 = rng.choice(ks)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
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


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _cost(k, G, D, darts, perms):
    if len({tuple(x) for x in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        seen = bytearray(N)
        seen[src] = 1
        fr = [src]
        cnt = 1
        for _ in range(D):
            nx = []
            for u in fr:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nx.append(v)
            cnt += len(nx)
            fr = nx
            if not fr:
                break
        total += N - cnt
    return total


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = _random_darts(d, k, G, rng)
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        if k == 1 or rng.random() < 0.75:
            idx = rng.randrange(len(darts))
            old_s, old_p = darts[idx][2], perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
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
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, perms, cost


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main build.
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
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    moore = lib.moore_bound(d, D)

    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n0, e0 = lib.projective_plane_incidence(q)
                consider(n0, e0)
                break
        if D >= 4:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    n0, e0 = _gq_w(q)
                    consider(n0, e0)
                    break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n0, e0 = lib.araujo_lopez_graph(d - 2)
                consider(n0, e0)
            except Exception:
                pass
        if best_n > 0:
            n1, e1 = _grow(best_n, best_e, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    loop_end = min(deadline, start + 0.8 * time_limit)
    ks = [1, 2, 3, 4]
    while time.monotonic() < loop_end and best_n < moore:
        # New: signed double cover of the current best graph.
        if rng.random() < 0.05:
            cover = _signed_cover(best_n, best_e, D,
                                  min(loop_end, time.monotonic() + 3.0), rng)
            if cover is not None:
                consider(2 * best_n, cover)
                continue

        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 6)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g

        iters = 600 if k == 1 else 300
        darts, perms, c = _anneal(d, D, k, order, mul, rng, loop_end, iters)
        N, E = _lift_edges(k, order, darts, perms)
        if c == 0:
            consider(N, E)
            continue

        if c <= 60 and rng.random() < 0.35 and time.monotonic() < loop_end:
            rep = _repair(N, E, D, min(loop_end, time.monotonic() + 4.0), rng)
            if rep is not None:
                n3, e3 = _saturate(rep[0], rep[1], d, rng)
                consider(n3, e3)
                n4, e4 = _grow(n3, e3, d, D, min(deadline, time.monotonic() + 3.0), rng)
                consider(n4, e4)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n = 2 * d
        best_e = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, [(int(u), int(v)) for u, v in best_e]
