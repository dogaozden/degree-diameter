import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
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
            if (i * P + j) in covered:
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
    """Incidence graph of W(q): degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _two_colour(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


def _conflicts(n, adj):
    """cs[v] = same-side vertices sharing a neighbour with v (two blown copies would overload it)."""
    cs = [set() for _ in range(n)]
    for w in range(n):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                cs[a[i]].add(a[j])
                cs[a[j]].add(a[i])
    return cs


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies with the same neighbourhood."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


# ----------------------------------------------------------------------------
# Independent-set searches on one side of a bipartite base.
# ----------------------------------------------------------------------------

def _ils(N, nb, rng, nprng, deadline):
    """Iterated local search for a large conflict-free subset of range(N)."""
    if N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        score[tabu > it] = np.inf
        v = int(np.argmin(score))
        return v if np.isfinite(score[v]) else -1

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > len(best):
                best = list(S)
                last_best_it = it
            v = pick()
            if v >= 0:
                add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if v >= 0:
                add(v)
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > len(best):
        best = list(S)
    return best


def _tabu_mis(n, adj, deadline, rng):
    """Tabu search for a large independent set (adj = neighbour lists, symmetric)."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        if not cands:
            continue
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


def _side_best(V, cs, rng, nprng, deadline):
    """Largest conflict-free subset of side V found by ILS and tabu search (best of both)."""
    if not V:
        return []
    idx = {v: i for i, v in enumerate(V)}
    nb = [[idx[w] for w in cs[v] if w in idx] for v in V]
    now = time.monotonic()
    half = now + max(0.0, deadline - now) / 2.0
    a = _ils(len(V), nb, rng, nprng, half)
    b = _tabu_mis(len(V), nb, deadline, rng)
    res = a if len(a) >= len(b) else b
    return [V[i] for i in res]


# ----------------------------------------------------------------------------
# Greedy set-cover extension using spare degree.
#
# A new vertex x joined to S keeps diameter <= D when every existing vertex lies
# within distance D-1 of some s in S. Existing distances can only shrink.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball(n, adj, R):
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


def _extend(n, edges, d, D, deadline, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _two_colour(n, adj)
    R = D - 1
    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball(n, adj, R)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Full generalized quadrangle W(d-1) when d-1 is a prime power (degree d).
    if D >= 4 and 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin blow-up of a (d-1)-regular base: W(d-2) for D >= 4, PG(2, d-2) for D = 3.
    q = d - 2
    base = None
    if 2 <= q <= 11 and lib.is_prime_power(q):
        try:
            if D >= 4:
                base = _gq_incidence(q)
            elif D == 3:
                base = lib.projective_plane_incidence(q)
        except Exception:
            base = None

    if base is not None and time.monotonic() < deadline - 1.0:
        try:
            n0, e0 = base
            consider(n0, e0)
            adj0 = lib.adjacency(n0, e0)
            if all(len(a) == d - 1 for a in adj0):
                color = _two_colour(n0, adj0)
                sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]
                cs = _conflicts(n0, adj0)
                mis_deadline = t0 + 0.6 * budget
                now = time.monotonic()
                total = max(0.0, mis_deadline - now)
                S = []
                S += _side_best(sides[0], cs, rng, nprng, now + 0.5 * total)
                S += _side_best(sides[1], cs, rng, nprng, mis_deadline)
                nb, eb = _blow(n0, e0, S)
                consider(nb, eb)
                nx, ex = _extend(nb, eb, d, D, deadline, rng)
                consider(nx, ex)
        except Exception:
            pass
    elif pg is not None and time.monotonic() < deadline - 1.0:
        try:
            nx, ex = _extend(pg[0], pg[1], d, D, deadline, rng)
            consider(nx, ex)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
