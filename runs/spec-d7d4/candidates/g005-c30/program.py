import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D = 3) and generalized quadrangle (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    lines = []
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
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q capped for build speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers for growing a graph by adding vertices and saturating degree.
# ----------------------------------------------------------------------------

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


def _saturate_edges(n, edges, d, rng):
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


def _cover_search(ball, cands, full, d, rng, budget):
    """Find <= d candidates whose radius balls cover `full`; return list or None."""
    used = set()
    chosen = []
    nodes = [0]

    def rec(covered, depth):
        if covered == full:
            return True
        if depth >= d or nodes[0] >= budget:
            return False
        nodes[0] += 1
        rem = full & ~covered
        free = [s for s in cands if s not in used]
        gains = {s: (ball[s] & rem).bit_count() for s in free}
        best = max(gains.values(), default=0)
        if best == 0 or rem.bit_count() > best * (d - depth):
            return False
        bits = []
        x = rem
        while x:
            low = x & -x
            bits.append(low.bit_length() - 1)
            x ^= low
        sample = rng.sample(bits, min(6, len(bits)))
        best_opts = None
        for w in sample:
            opts = [s for s in free if gains[s] and (ball[s] >> w) & 1]
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        if not best_opts:
            return False
        rng.shuffle(best_opts)
        best_opts.sort(key=lambda s: -gains[s])
        for s in best_opts:
            used.add(s)
            chosen.append(s)
            if rec(covered | ball[s], depth + 1):
                return True
            used.discard(s)
            chosen.pop()
            if nodes[0] >= budget:
                break
        return False

    return list(chosen) if rec(0, 0) else None


def _grow_exact(n, edges, d, D, deadline, rng, budget):
    """Repeatedly add a vertex whose neighbourhood exactly covers the graph within D-1."""
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
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            if not cands:
                continue
            chosen = _cover_search(ball, cands, full, d, rng, budget)
            if chosen:
                v = n
                n += 1
                color.append(c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                placed = True
                break
        if not placed:
            break
    return n, edges


# ----------------------------------------------------------------------------
# NEW (bold): bi-Cayley graphs over small NON-abelian groups, searched for
# diameter 4 with a two-source cost.
#
# For a finite group G and a d-subset S of G, define the bipartite graph with
# parts A = {a_x} and B = {b_y}, x, y in G, and edges a_x ~ b_{x s} (s in S).
# Left multiplication by g is an automorphism (a_x -> a_{gx}, b_y -> b_{gy}),
# so all A-vertices are equivalent and all B-vertices are equivalent. Hence
#   diameter <= 4  <=>  every vertex lies within distance 4 of a_e and of b_e,
# where e is the identity. Each cost evaluation is therefore just two small BFS
# runs. The graph is bipartite by construction and d-regular on 2|G| vertices.
#
# Groups come from lib.cyclic_group and lib.semidirect_group, so non-abelian
# groups Z_m x| Z_k are included. Orders are scanned upward and simulated
# annealing searches the subset S for each order.
# ----------------------------------------------------------------------------

def _tables(order, mul, inv):
    """Multiplication table mt[x][y] = x*y and inverse list iv[x] for a group of given order."""
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    iv = [inv(x) for x in range(order)]
    return mt, iv


def _candidate_groups(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k with m*k = N."""
    cyc = lib.cyclic_group(N)
    rest = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                rest.append(lib.semidirect_group(m, k, r))
    rng.shuffle(rest)
    return [cyc] + rest[:4]


def _bicayley_cost(S, N, mt, iv):
    """Sum over the two sources a_e (index 0) and b_e (index N) of unreached vertices within distance 4."""
    sinv = [iv[s] for s in S]
    total = 0
    for start in (0, N):
        vis = bytearray(2 * N)
        vis[start] = 1
        frontier = [start]
        reached = 1
        for _ in range(4):
            nxt = []
            for v in frontier:
                if v < N:
                    row = mt[v]
                    for s in S:
                        w = N + row[s]
                        if not vis[w]:
                            vis[w] = 1
                            nxt.append(w)
                else:
                    row = mt[v - N]
                    for t in sinv:
                        w = row[t]
                        if not vis[w]:
                            vis[w] = 1
                            nxt.append(w)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - reached
    return total


def _bicayley_sa(N, d, mt, iv, rng, deadline, iters):
    """Annealed search for a d-subset S with zero cost; return S or None."""
    S = rng.sample(range(N), d)
    c = _bicayley_cost(S, N, mt, iv)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _bicayley_cost(T, N, mt, iv)
        if ct <= c or rng.random() < math.exp(-(ct - c) / 0.6):
            S, c = T, ct
    return S if c == 0 else None


def _group_sweep(d, N0, N1, deadline, rng, consider):
    """Scan group orders N upward; for each, search groups and subsets for a diameter-4 graph on 2N vertices."""
    N = N0
    fails = 0
    while N <= N1 and fails < 6 and time.monotonic() < deadline:
        found = None
        found_mt = None
        for (order, mul, inv) in _candidate_groups(N, rng):
            if time.monotonic() >= deadline:
                break
            mt, iv = _tables(order, mul, inv)
            S = _bicayley_sa(N, d, mt, iv, rng, deadline, 2500)
            if S is not None:
                found, found_mt = S, mt
                break
        if found is not None:
            edges = [(x, N + found_mt[x][s]) for x in range(N) for s in found]
            consider(2 * N, edges)
            fails = 0
        else:
            fails += 1
        N += 1


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 4 and d >= 3:
        # Non-abelian bi-Cayley graphs searched directly for diameter 4.
        moore_half = 1 + (d - 1) + (d - 1) ** 2 + (d - 1) ** 3
        N0 = max(d + 1, (moore_half * 2) // 3)
        _group_sweep(d, N0, moore_half, start + 0.6 * time_limit, rng, consider)

    if D >= 4:
        # Generalized quadrangle base, then exact-cover growth with spare degree.
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            base_n, base_e = gq
            grow_end = start + 0.88 * time_limit
            attempt = 0
            while time.monotonic() < grow_end:
                arng = random.Random(seed * 1000003 + attempt)
                n2, e2 = _grow_exact(base_n, base_e, d, D, grow_end, arng, 1500)
                e2 = _saturate_edges(n2, e2, d, arng)
                consider(n2, e2)
                attempt += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
