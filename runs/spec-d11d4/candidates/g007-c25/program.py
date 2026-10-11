import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Points and totally isotropic lines of the symplectic generalized quadrangle W(q).

    Returns (P, lines): points are indexed 0..P-1 and each line is a sorted list of point indices.
    """
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if i * P + j in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): degree q+1, diameter 4, points then lines."""
    P, lines = _gq_w(q)
    return P + len(lines), [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Generic graph helpers
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    return color


def _ball(n, adj, r):
    """Bitmask per vertex of all vertices at distance <= r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


# ----------------------------------------------------------------------------
# Maximum independent set (ILS with conflict repair), restricted to a vertex mask
# ----------------------------------------------------------------------------

def _mis(n, nbrs, allowed, deadline, rng, nprng):
    """Large independent set among allowed vertices of the conflict graph nbrs."""
    if not allowed.any():
        return []
    cnt = np.zeros(n, dtype=np.int64)
    inS = np.zeros(n, dtype=bool)
    tabu = np.zeros(n, dtype=np.int64)
    size = 0
    best = []
    best_size = 0
    last = 0
    it = 0
    while True:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        bad = np.flatnonzero(inS & (cnt > 0))
        if bad.size:
            u = int(bad[rng.randrange(bad.size)])
            inS[u] = False
            cnt[nbrs[u]] -= 1
            size -= 1
            tabu[u] = it + 7 + rng.randrange(8)
        elif size > best_size:
            best_size = size
            best = np.flatnonzero(inS).tolist()
            last = it
        sc = cnt + nprng.random(n)
        sc[~allowed | inS | (tabu > it)] = np.inf
        v = int(np.argmin(sc))
        if np.isfinite(sc[v]):
            inS[v] = True
            cnt[nbrs[v]] += 1
            size += 1
        if it - last > 3000:
            members = np.flatnonzero(inS).tolist()
            if members:
                k = min(len(members), max(1, len(members) // 5))
                for x in rng.sample(members, k):
                    inS[x] = False
                    cnt[nbrs[x]] -= 1
                    size -= 1
                    tabu[x] = it + 5
            last = it
    return best


def _blow(n0, e0, S):
    """Twin blow-up: each vertex in S gets one extra copy with the same neighbourhood."""
    extra = {}
    for v in S:
        if v not in extra:
            extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = [(a, b) for u, v in e0 for a in copies[u] for b in copies[v]]
    return n0 + len(extra), edges


def _blow_search(n0, e0, d, deadline, rng, nprng):
    """Find S with each vertex having at most one S-neighbour (base degree d-1), then blow up."""
    adj = [[] for _ in range(n0)]
    for u, v in e0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    color = _two_color(n0, adj)
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    nbrs = [np.array(sorted(s), dtype=np.int64) for s in cs]
    now = time.monotonic()
    R = deadline - now
    if R <= 0.5:
        return None
    col = np.asarray(color)
    S = []
    S += _mis(n0, nbrs, col == 0, now + 0.5 * R, rng, nprng)
    S += _mis(n0, nbrs, col == 1, now + R, rng, nprng)
    return _blow(n0, e0, S)


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension (radius D-1)
#
# A new vertex x on one side, joined to S on the other side, keeps diameter D iff
# the balls of radius D-1 around S cover all existing vertices. Adding x never
# lengthens paths, so only this cover condition needs checking.
# ----------------------------------------------------------------------------

def _extend(n, edges, d, D, deadline, rng):
    r = D - 1
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _two_color(n, adj)
    while time.monotonic() < deadline:
        reach = _ball(n, adj, r)
        full = (1 << n) - 1
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        added = False
        for _ in range(300):
            if time.monotonic() >= deadline:
                break
            s0 = spare[rng.randrange(len(spare))]
            pool = [v for v in spare if v != s0 and color[v] == color[s0]]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bg = 0
                bv = -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > bg:
                        bg = g
                        bv = v
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            added = True
            break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + total
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

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

    if D == 2:
        return best

    pg = _pg(d) if D >= 3 else None
    if pg is not None:
        consider(*pg)

    # W(d-1) has degree d and diameter 4 (no spare degree).
    if D >= 4 and 2 <= d - 1 <= 9 and lib.is_prime_power(d - 1) and total > 10:
        consider(*_gq_incidence(d - 1))

    # Primary base of degree d-1: blow-up plus extension.
    q = d - 2
    primary = None
    if total > 10 and q >= 2 and lib.is_prime_power(q):
        if D == 3:
            primary = lib.projective_plane_incidence(q)
        elif D >= 4 and q <= 9:
            primary = _gq_incidence(q)

    if primary is not None:
        n0, e0 = primary
        consider(n0, e0)
        cur = primary
        blow_deadline = t0 + 0.7 * total
        blown = _blow_search(n0, e0, d, blow_deadline, rng, nprng)
        if blown is not None and lib.is_valid(blown[0], blown[1], d, D):
            consider(*blown)
            cur = blown
        ext = _extend(cur[0], cur[1], d, D, deadline - 1.0, rng)
        consider(*ext)
    elif pg is not None:
        ext = _extend(pg[0], pg[1], d, D, deadline - 1.0, rng)
        consider(*ext)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
