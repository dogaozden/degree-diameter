import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baseline for D = 3: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover vertices, then edge saturation.
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
    """Extend by cover vertices first, then saturate edges with the leftover spare degree.

    Input must already satisfy diameter D; the caller re-validates the output.
    """
    cur_n, cur_e = n, list(edges)
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: non-metacyclic group catalog for bi-Cayley lifts.
#
# Groups are given by keys:
#   ("lf", p, pgl)   linear fractional group PSL(2,p) (pgl=False) or PGL(2,p),
#                    realised as permutations of the projective line over Z_p;
#   ("cyc", m)       cyclic group Z_m;
#   ("prod", k1, k2) direct product of two catalog groups.
# Each group is a multiplication table with identity at index 0, so the
# bi-Cayley hill-climb (A_x ~ B_{x g}, g in S) works unchanged.
# PSL(2,7) (168) and PGL(2,7) (336) are not semidirect products of cyclic
# groups, so they add connection-set families the semidirect sweep misses.
# ----------------------------------------------------------------------------

def _order(key):
    """Order of a catalog group, computed from its key without building it."""
    if key[0] == "lf":
        p = key[1]
        base = p * (p * p - 1)
        return base if key[2] else base // 2
    if key[0] == "cyc":
        return key[1]
    return _order(key[1]) * _order(key[2])


def _lf_elements(p, pgl):
    """Permutations of P^1(Z_p) induced by SL(2,p) (or GL(2,p)), identity first, deduplicated."""
    ident = tuple(range(p + 1))
    elems = [ident]
    seen = {ident}

    def inv(x):
        return pow(x, p - 2, p)

    for a, b, c, dd in itertools.product(range(p), repeat=4):
        det = (a * dd - b * c) % p
        if det == 0 or (det != 1 and not pgl):
            continue
        perm = []
        for x in range(p):
            den = (c * x + dd) % p
            perm.append(p if den == 0 else ((a * x + b) % p) * inv(den) % p)
        perm.append(p if c % p == 0 else a * inv(c) % p)
        pt = tuple(perm)
        if pt not in seen:
            seen.add(pt)
            elems.append(pt)
    return elems


_GROUP_CACHE = {}


def _get_group(key):
    """Return (N, T, invs) for a catalog group; T[x][g] = x*g, identity is 0."""
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    kind = key[0]
    if kind == "lf":
        elems = _lf_elements(key[1], key[2])
        N = len(elems)
        L = len(elems[0])
        index = {e: i for i, e in enumerate(elems)}
        T = [[index[tuple(ei[ej[t]] for t in range(L))] for ej in elems] for ei in elems]
    elif kind == "cyc":
        m = key[1]
        N = m
        T = [[(x + y) % m for y in range(m)] for x in range(m)]
    else:
        _, k1, k2 = key
        N1, T1, _u1 = _get_group(k1)
        N2, T2, _u2 = _get_group(k2)
        N = N1 * N2
        T = []
        for x in range(N):
            a, b = divmod(x, N2)
            r1 = T1[a]
            r2 = T2[b]
            row = [0] * N
            for y in range(N):
                c, dd = divmod(y, N2)
                row[y] = r1[c] * N2 + r2[dd]
            T.append(row)
    invs = [0] * N
    for g in range(N):
        row = T[g]
        for h in range(N):
            if row[h] == 0:
                invs[g] = h
                break
    val = (N, T, invs)
    if len(_GROUP_CACHE) >= 12:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = val
    return val


CATALOG = [
    ("lf", 5, False), ("lf", 5, True), ("lf", 7, False), ("lf", 7, True),
    ("prod", ("lf", 5, False), ("cyc", 3)),
    ("prod", ("lf", 5, False), ("cyc", 4)),
    ("prod", ("lf", 5, True), ("cyc", 2)),
    ("prod", ("lf", 5, False), ("cyc", 5)),
    ("prod", ("lf", 7, False), ("cyc", 2)),
    ("prod", ("lf", 3, True), ("cyc", 8)),
    ("prod", ("lf", 3, True), ("cyc", 12)),
]


# ----------------------------------------------------------------------------
# Bi-Cayley hill-climb over a group table (shared by catalog and semidirect).
# ----------------------------------------------------------------------------

CLIMB_ITERS = 600
MAX_SEMI_GROUPS = 8
BAND_EXTRA = 12


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _semi_tables(m, k, r):
    """(N, T, invs) for Z_m x|_r Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return order, T, invs


def _unreached(N, T, invs, S, D):
    """Count vertex pairs not within distance D, from A_0 and B_0.

    Left translation is an automorphism acting transitively on A and on B,
    so eccentricities from A_0 and B_0 determine the diameter.
    """
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed as one dart) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    grow_slice = max(0.3, 0.06 * budget)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    def consider_grown(n, e):
        """Validate a found graph, then try to extend it."""
        if not lib.is_valid(n, e, d, D):
            return
        consider(n, e)
        if best[0] < moore:
            gn, ge = _grow(n, e, d, D,
                           min(deadline, time.monotonic() + grow_slice), rng)
            consider(gn, ge)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if best[0] < moore:
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * budget, rng)
                consider(n2, e2)

    # Main search: bi-Cayley lifts aiming above the current best order.
    sweep_next = None
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break

        if rng.random() < 0.6:
            # NEW: catalog groups (PSL/PGL(2,p) and their products).
            cands = [k for k in CATALOG
                     if lo <= _order(k) <= moore // 2 and _order(k) >= d]
            if not cands:
                continue
            cands.sort(key=_order)
            key = cands[rng.randrange(min(3, len(cands)))]
            N, T, invs = _get_group(key)
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider_grown(2 * N, edges)
        else:
            # Semidirect sweep over orders just above the lower bound.
            if sweep_next is None or sweep_next < lo or sweep_next > lo + BAND_EXTRA:
                sweep_next = lo
            N = sweep_next
            sweep_next += 1
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, r in groups[:MAX_SEMI_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, T, invs = _semi_tables(m, k2, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider_grown(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
