import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane PG(2, q) (D = 3) and generalized quadrangle W(q) (D >= 4).
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


# ----------------------------------------------------------------------------
# Twin augmentation: a twin shares the neighbourhood of an existing vertex.
# This keeps diameter and bipartiteness, and uses spare degree on neighbours.
# ----------------------------------------------------------------------------

def _adj_list(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _twin_packing(n, adj, slack, rng, deadline):
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    if not cand:
        return []
    inset = [False] * n
    load = [0] * n

    def take(x):
        inset[x] = True
        for w in adj[x]:
            load[w] += 1

    def drop(x):
        inset[x] = False
        for w in adj[x]:
            load[w] -= 1

    def fill(order):
        for x in order:
            if not inset[x] and all(load[w] < slack[w] for w in adj[x]):
                take(x)

    order = cand[:]
    rng.shuffle(order)
    fill(order)
    best = [x for x in cand if inset[x]]
    while time.monotonic() < deadline:
        chosen = [x for x in cand if inset[x]]
        for x in rng.sample(chosen, min(rng.randint(1, 3), len(chosen))):
            drop(x)
        order = cand[:]
        rng.shuffle(order)
        fill(order)
        cur = sum(1 for x in cand if inset[x])
        if cur > len(best):
            best = [x for x in cand if inset[x]]
        elif cur < len(best) - 2 or rng.random() < 0.01:
            for x in cand:
                if inset[x]:
                    drop(x)
            for x in best:
                take(x)
    return best


def _twin_augment(n, edges, d, rng, deadline):
    adj = _adj_list(n, edges)
    slack = [max(0, d - len(a)) for a in adj]
    chosen = _twin_packing(n, adj, slack, rng, deadline)
    E = list(edges)
    N = n
    for x in chosen:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# New construction: bi-Cayley bipartite graphs over Z_m with k base vertices per
# side. Vertex a_{i,x} (i < k, x in Z_m) and b_{j,y} are indexed as i*m+x and
# (k+j)*m+y. A dart family is given by d permutations sig[t] of range(k) and
# shifts shift[t][i] in Z_m: a_{i,x} ~ b_{sig[t][i], x + shift[t][i]} for all t.
# Every vertex has degree exactly d, and the graph is bipartite by construction.
#
# Translation x -> x+c is an automorphism, so the diameter test only needs BFS
# from a_{i,0} and b_{j,0} (one source per base vertex). Cost = unreached pairs.
# Simulated annealing over shifts and permutations finds zero-cost graphs.
# ----------------------------------------------------------------------------

def _bc_ball(k, m, d, sig, sig_inv, shift, src, D):
    N = 2 * k * m
    km = k * m
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < km:
                i, x = divmod(u, m)
                for t in range(d):
                    v = (k + sig[t][i]) * m + (x + shift[t][i]) % m
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                j, y = divmod(u - km, m)
                for t in range(d):
                    i = sig_inv[t][j]
                    v = i * m + (y - shift[t][i]) % m
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return count


def _bc_cost(k, m, d, sig, sig_inv, shift, D, limit):
    N = 2 * k * m
    total = 0
    for src in range(0, N, m):  # one source per base vertex (both sides)
        total += N - _bc_ball(k, m, d, sig, sig_inv, shift, src, D)
        if total > limit:
            return total
    return total


def _dup_ok(d, sig, shift, i):
    """Vertex a_{i,.} must have d distinct (neighbour block, shift) pairs, else multi-edges."""
    pairs = {(sig[t][i], shift[t][i]) for t in range(d)}
    return len(pairs) == d


def _swap(sig, sig_inv, t, i1, i2):
    a, b = sig[t][i1], sig[t][i2]
    sig[t][i1], sig[t][i2] = b, a
    sig_inv[t][b] = i1
    sig_inv[t][a] = i2


def _bc_edges(k, m, d, sig, shift):
    E = []
    for t in range(d):
        for i in range(k):
            j = sig[t][i]
            for x in range(m):
                E.append((i * m + x, (k + j) * m + (x + shift[t][i]) % m))
    return 2 * k * m, E


def _bc_search(d, D, k, m, deadline, rng):
    if d > k * m:
        return None
    sig = None
    shift = None
    for _ in range(1000):
        sig = [rng.sample(range(k), k) for _ in range(d)]
        shift = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
        if all(_dup_ok(d, sig, shift, i) for i in range(k)):
            break
    else:
        return None
    sig_inv = [[0] * k for _ in range(d)]
    for t in range(d):
        for i in range(k):
            sig_inv[t][sig[t][i]] = i

    cost = _bc_cost(k, m, d, sig, sig_inv, shift, D, float("inf"))
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 2.0 * (0.05 / 2.0) ** ((now - t0) / span)
        if k == 1 or rng.random() < 0.5:
            t = rng.randrange(d)
            i = rng.randrange(k)
            old = shift[t][i]
            new = rng.randrange(m)
            if new == old:
                continue
            shift[t][i] = new
            if not _dup_ok(d, sig, shift, i):
                shift[t][i] = old
                continue
            nc = _bc_cost(k, m, d, sig, sig_inv, shift, D, float("inf"))
            if nc <= cost or rng.random() < math.exp((cost - nc) / T):
                cost = nc
            else:
                shift[t][i] = old
        else:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            _swap(sig, sig_inv, t, i1, i2)
            if not (_dup_ok(d, sig, shift, i1) and _dup_ok(d, sig, shift, i2)):
                _swap(sig, sig_inv, t, i1, i2)
                continue
            nc = _bc_cost(k, m, d, sig, sig_inv, shift, D, float("inf"))
            if nc <= cost or rng.random() < math.exp((cost - nc) / T):
                cost = nc
            else:
                _swap(sig, sig_inv, t, i1, i2)
    if cost == 0:
        return _bc_edges(k, m, d, sig, shift)
    return None


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    end = start + 0.80 * time_limit

    # Algebraic bases plus twin augmentation (both preserve diameter).
    bases = []
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
    if D >= 4:
        qs = [q for q in range(min(d - 1, 6), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            bases.append(_gq_w(q))
    for idx, (bn, be) in enumerate(bases):
        consider(bn, be)
        tn, te = _twin_augment(bn, be, d, rng,
                               min(end, start + 0.05 * time_limit * (idx + 1)))
        consider(tn, te)

    if best_n >= moore:
        return best

    # New construction: bi-Cayley search over Z_m with k base vertices per side.
    ks = [2, 3, 4, 6, 1]
    idx = 0
    while time.monotonic() < end and best_n < moore:
        k = ks[idx % len(ks)]
        idx += 1
        m = best_n // (2 * k) + 1  # order 2km strictly exceeds the current best
        if m < 2:
            continue
        now = time.monotonic()
        slice_end = min(end, now + max(3.0, 0.08 * time_limit))
        res = _bc_search(d, D, k, m, slice_end, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
