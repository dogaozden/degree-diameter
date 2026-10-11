import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic bases: projective plane (D >= 3) and generalized quadrangle W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k2 with k blocks per side.
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s}. Left multiplication is an
# automorphism, so distances need to be measured from one vertex per layer.
# Search: tabu-guided steepest descent over sampled moves (a different
# acceptance rule from simulated annealing).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 3, 4, 6])
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


def _cost(k, G, D, adj):
    """Total unreached (representative, vertex) pairs within distance D. Zero means valid."""
    N = 2 * k * G
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _lift_adj(k, G, ptab, darts):
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = ptab[s]
        ba, bb = i * G, (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _evaluate(k, G, D, ptab, darts):
    if len({(a, b, c) for a, b, c in darts}) < len(darts):
        return _BIG
    return _cost(k, G, D, _lift_adj(k, G, ptab, darts))


def _lift_edges(k, G, ptab, darts):
    E = set()
    for i, j, s in darts:
        pm = ptab[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_search(d, D, k, G, ptab, rng, deadline):
    """Tabu-guided steepest descent over sampled moves. Returns darts with cost 0, or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cur = _evaluate(k, G, D, ptab, darts)
    tabu = {}
    step = 0
    tenure = 5
    while cur > 0 and time.monotonic() < deadline:
        step += 1
        best_move, best_c = None, None
        for _ in range(12):
            if rng.random() < 0.6 or k == 1:
                idx = rng.randrange(len(darts))
                old = darts[idx][2]
                new = rng.randrange(G)
                if new == old:
                    continue
                key = ("s", idx)
                darts[idx][2] = new
                c = _evaluate(k, G, D, ptab, darts)
                darts[idx][2] = old
                move = ("s", idx, new)
            else:
                L = rng.randrange(d)
                a, b = rng.sample(range(k), 2)
                ia, ib = L * k + a, L * k + b
                key = ("p", L)
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                c = _evaluate(k, G, D, ptab, darts)
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                move = ("p", ia, ib)
            if tabu.get(key, -1) > step and c >= cur:
                continue
            if best_c is None or c < best_c:
                best_c, best_move, best_key = c, move, key
        if best_move is None:
            continue
        if best_move[0] == "s":
            darts[best_move[1]][2] = best_move[2]
        else:
            ia, ib = best_move[1], best_move[2]
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        cur = best_c
        tabu[best_key] = step + tenure
    return darts if cur == 0 else None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bound = lib.moore_bound(d, D)

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
    except Exception:
        pass
    if best[0] >= bound:
        return best

    try:
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass
    if best[0] >= bound:
        return best

    # Main search: tabu-guided voltage lifts over semidirect groups with 2-4 blocks per side.
    ks = [2, 2, 3, 3, 4]
    while time.monotonic() < deadline and best[0] < bound:
        try:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(4))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            ptab = [[mul(x, s) for x in range(order)] for s in range(order)]
            local_deadline = min(deadline, time.monotonic() + 6.0)
            darts = _lift_search(d, D, k, order, ptab, rng, local_deadline)
            if darts is not None:
                n, e = _lift_edges(k, order, ptab, darts)
                consider(n, e)
        except Exception:
            continue

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
