import itertools
import math
import random
import time

import lib

GROUPS_PER_ATTEMPT = 4      # groups tried per (base shape, order) attempt
ANNEAL_ITERS = 1200         # voltage mutations per group
SLICE = 4.0                 # seconds per attempt before moving on
SAFETY = 6.0                # seconds kept in reserve from time_limit


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: multi-vertex base graph lifted over a finite group.
#
# Base: a fibres on the left (A_i) and a fibres on the right (B_j), with a
# circulant multiplicity pattern c (sum c = d, all parts >= 1): the block
# (i, j) carries k = c[(j - i) mod a] darts. Each dart is a group element
# g, joining A_{i,x} to B_{j, x*g} for every x in G. Left multiplication is
# an automorphism, so eccentricities are constant on fibres, and it is enough
# to check one source per fibre (2a sources). Voltages within a block are
# distinct, so the lift is simple and exactly d-regular.
# ----------------------------------------------------------------------------

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


def _compositions(total, parts):
    """All tuples of `parts` positive integers summing to `total`."""
    if parts == 1:
        return [(total,)] if total >= 1 else []
    out = []
    for first in range(1, total - parts + 2):
        for rest in _compositions(total - first, parts - 1):
            out.append((first,) + rest)
    return out


def _canon(c):
    """Canonical rotation of a multiplicity tuple."""
    a = len(c)
    return min(tuple(c[i:]) + tuple(c[:i]) for i in range(a))


def _reach(src, adj, V, D):
    """Number of vertices within distance D of src (including src)."""
    seen = bytearray(V)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = 1
                    nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return cnt


def _cost(N, a, blocks, vols, T, D):
    """Total unreached (source, vertex) pairs over the 2a fibre representatives."""
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    for b, (i, j, _k) in enumerate(blocks):
        base_a = i * N
        base_b = a * N + j * N
        for g in vols[b]:
            for x in range(N):
                u = base_a + x
                w = base_b + T[x][g]
                adj[u].append(w)
                adj[w].append(u)
    total = 0
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    for s in sources:
        total += V - _reach(s, adj, V, D)
    return total


def _anneal(N, a, c, D, T, rng, iters, deadline):
    """Anneal voltages (distinct within each block) to zero unreached pairs."""
    blocks = []
    for i in range(a):
        for j in range(a):
            blocks.append((i, j, c[(j - i) % a]))
    vols = [rng.sample(range(N), k) for (_, _, k) in blocks]
    slots = [(b, t) for b, (_, _, k) in enumerate(blocks) for t in range(k)]
    cur = _cost(N, a, blocks, vols, T, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        b, t = rng.choice(slots)
        g = rng.randrange(N)
        if g in vols[b]:
            continue
        old = vols[b][t]
        vols[b][t] = g
        new = _cost(N, a, blocks, vols, T, D)
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            vols[b][t] = old
    if cur != 0:
        return None
    return blocks, vols


def _try(N, a, c, D, rng, deadline):
    """Try a few groups of order N for base shape (a, c)."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        res = _anneal(N, a, c, D, T, rng, ANNEAL_ITERS, deadline)
        if res is not None:
            blocks, vols = res
            return T, blocks, vols
    return None


def _edges_from(N, a, T, blocks, vols):
    edges = []
    for b, (i, j, _k) in enumerate(blocks):
        for g in vols[b]:
            for x in range(N):
                edges.append((i * N + x, a * N + j * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - SAFETY))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact record family for D = 3, d - 1 prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Base shapes: a fibres per side, circulant multiplicities summing to d.
    configs = []
    seen = set()
    for a in (2, 3, 4):
        if a > d:
            continue
        for c in _compositions(d, a):
            key = (a, _canon(c))
            if key in seen:
                continue
            seen.add(key)
            configs.append({"a": a, "c": _canon(c), "N": max(d, best_n // (2 * a) + 1)})

    while configs and time.monotonic() < deadline:
        for cfg in configs:
            now = time.monotonic()
            if now >= deadline:
                break
            a, c = cfg["a"], cfg["c"]
            cfg["N"] = max(cfg["N"], max(d, best_n // (2 * a) + 1))
            N = cfg["N"]
            att_deadline = min(deadline, now + SLICE)
            res = _try(N, a, c, D, rng, att_deadline)
            if res is None:
                continue
            T, blocks, vols = res
            edges = _edges_from(N, a, T, blocks, vols)
            consider(2 * a * N, edges)
            cfg["N"] = N + 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
