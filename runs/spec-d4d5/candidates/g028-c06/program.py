import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane and generalized-quadrangle starting graphs (valid, diameter 3 / 4).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Helpers shared by the search families.
# ----------------------------------------------------------------------------

def _consider(best, n, E, d, D):
    """Replace best = [n, edges] if (n, E) is strictly larger and exactly valid."""
    if n > best[0] and lib.is_valid(n, E, d, D):
        best[0] = n
        best[1] = [tuple(e) for e in E]
        return True
    return False


def _badpairs(n, adj, D):
    """Number of unordered pairs at distance > D (bitset BFS over adjacency lists)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# NEW PRIMARY FAMILY: vertex-pair growth followed by edge-swap annealing.
#
# State: bipartite graph given by edge list E of (a, b) with a on side 0 and b on
# side 1, max degree d. Moves:
#   * swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Preserves all degrees and bipartiteness.
#   * grow: add a new side-0 vertex A and side-1 vertex B. Pick d edges (a_i,b_i)
#     with distinct endpoints, replace them by (a_i,B) and (A,b_i). Degrees are preserved,
#     and A and B each get degree d.
# Cost = number of vertex pairs at distance > D. Annealing drives cost to zero.
# ----------------------------------------------------------------------------

def _grow_pair(n, E, d, rng):
    """Return (n + 2, new_E) after adding one A-vertex and one B-vertex, or None."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedA, usedB, chosen = set(), set(), []
    for i in idx:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    A, B = n, n + 1
    cs = set(chosen)
    newE = [E[i] for i in range(len(E)) if i not in cs]
    for i in chosen:
        a, b = E[i]
        newE.append((a, B))
        newE.append((A, b))
    return n + 2, newE


def _swap(E, adj, eset, i, j):
    """Apply the double-edge swap on indices i, j. It is an involution, so it also undoes itself."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    adj[a1].append(b2)
    adj[b2].append(a1)
    adj[a2].append(b1)
    adj[b1].append(a2)
    eset.discard((a1, b1))
    eset.discard((a2, b2))
    eset.add((a1, b2))
    eset.add((a2, b1))
    E[i] = [a1, b2]
    E[j] = [a2, b1]


def _anneal_zero(n, E, d, D, rng, deadline, iters):
    """Anneal edge swaps until every pair is within D. Returns (True, E) or (False, None)."""
    E = [list(e) for e in E]
    m = len(E)
    if m < 2:
        return False, None
    eset = set((a, b) for a, b in E)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    cost = _badpairs(n, adj, D)
    if cost == 0:
        return True, [tuple(e) for e in E]
    for it in range(iters):
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        _swap(E, adj, eset, i, j)
        c2 = _badpairs(n, adj, D)
        T = max(0.2, 1.5 * (1.0 - it / max(1, iters)))
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return True, [tuple(e) for e in E]
        else:
            _swap(E, adj, eset, i, j)
    return False, None


def _sa_growth(best, d, D, rng, deadline):
    """Repeatedly grow the current valid graph by one vertex pair and repair it by annealing."""
    cur_n = best[0]
    cur_E = [tuple(e) for e in best[1]]
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        g = _grow_pair(cur_n, cur_E, d, rng)
        if g is None:
            break
        gn, gE = g
        if gn > lib._moore_bound(d, D):
            break
        ok, E2 = _anneal_zero(gn, gE, d, D, rng, deadline, 600 * (1 + fails))
        if ok and _consider(best, gn, E2, d, D):
            cur_n = gn
            cur_E = [tuple(e) for e in E2]
            fails = 0
        else:
            fails += 1


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k (annealed).
# Used first to supply a strong starting graph for the growth family.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 6])
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
    return [mul(g, s) for g in range(G)]


def _cost_lift(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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


def _edges_lift(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_lift(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
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
            c2 = _cost_lift(k, G, D, darts, perms)
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
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_lift(k, G, darts, perms)
    return None


def _lift_phase(d, D, best, rng, deadline):
    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, deadline, 1500)
        if res is not None:
            _consider(best, res[0], res[1], d, D)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    kdd = [(i, d + j) for i in range(d) for j in range(d)]
    best = [2 * d, kdd]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            _consider(best, pg[0], pg[1], d, D)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            _consider(best, gq[0], gq[1], d, D)

    # Already at the Moore bound: nothing larger exists.
    if best[0] >= lib._moore_bound(d, D):
        return best[0], best[1]

    # Phase 1: voltage lifts supply a strong starting graph.
    if D >= 3:
        _lift_phase(d, D, best, rng, start + 0.4 * budget)

    # Phase 2: grow the best graph vertex-pair by vertex-pair, repairing by annealing.
    _sa_growth(best, d, D, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2 * d, kdd
    return best[0], best[1]
