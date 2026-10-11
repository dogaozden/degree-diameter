import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points of PG(3,q) with a symplectic form,
# totally isotropic lines.
# ----------------------------------------------------------------------------

def _w_points(q):
    """Return (points, index): normalised points of PG(3,q) and a tuple -> index dict."""
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    return pts, {v: i for i, v in enumerate(pts)}


def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts, index = _w_points(q)
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
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# NEW: explicit regular spread of W(q).
# Symmetric 2x2 matrices M(s,t) = [[s, lam*t], [lam*t, gam*s + dl*t]] form a
# 2-dimensional family whose nonzero members are all invertible (det is an
# anisotropic binary form). Then the lines {(x, Mx)} plus {(0, u)} are
# totally isotropic and partition the points: a regular spread of W(q).
# This gives q^2+1 pairwise disjoint lines (the maximum) for line twins.
# ----------------------------------------------------------------------------

def _norm_field(F, v):
    c = next(x for x in v if x)
    ic = F.inv(c)
    return tuple(F.mul(ic, x) for x in v)


def _find_spread_triple(F, q):
    for lam in range(1, q):
        for gam in range(q):
            for dl in range(q):
                ok = True
                for s in range(q):
                    for t in range(q):
                        if s == 0 and t == 0:
                            continue
                        a = s
                        b = F.mul(lam, t)
                        c = F.add(F.mul(gam, s), F.mul(dl, t))
                        if F.add(F.mul(a, c), F.neg(F.mul(b, b))) == 0:
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    return (lam, gam, dl)
    return None


def _regular_spread(q, pidx):
    """Return the q^2+1 lines of a regular spread of W(q) as sorted point-index lists (indices from pidx)."""
    F = lib.GF(q)
    triple = _find_spread_triple(F, q)
    if triple is None:
        return []
    lam, gam, dl = triple
    out = []
    for s in range(q):
        for t in range(q):
            a = s
            b = F.mul(lam, t)
            c = F.add(F.mul(gam, s), F.mul(dl, t))
            ids = set()
            for x0 in range(q):
                for x1 in range(q):
                    if x0 == 0 and x1 == 0:
                        continue
                    u0 = F.add(F.mul(a, x0), F.mul(b, x1))
                    u1 = F.add(F.mul(b, x0), F.mul(c, x1))
                    ids.add(pidx[_norm_field(F, (x0, u0, x1, u1))])
            out.append(sorted(ids))
    ids = set()
    for u0 in range(q):
        for u1 in range(q):
            if u0 or u1:
                ids.add(pidx[_norm_field(F, (0, u0, 0, u1))])
    out.append(sorted(ids))
    return out


# ----------------------------------------------------------------------------
# NEW: k-fixed tabu search for a maximum independent set.
# Keeps S, minimises conflicting edges inside S, and grows S whenever it is
# conflict-free. Moves are swaps: a conflicted vertex leaves, the least
# conflicted outside vertex enters. Tabu tenures stop immediate reversal.
# ----------------------------------------------------------------------------

def _tabu_is(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    adjset = [set(a) for a in adj]
    inS = [False] * n
    conf = [0] * n
    S = set()
    cost = [0]

    def add(v):
        cost[0] += conf[v]
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            conf[w] += 1

    def remove(u):
        cost[0] -= conf[u]
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            conf[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and conf[v] == 0:
            add(v)
    best = list(S)
    tin = [0] * n    # iteration before which v may not re-enter S
    tout = [0] * n   # iteration before which v may not leave S
    it = 0
    last = 0
    while True:
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        it += 1
        if cost[0] == 0:
            if len(S) > len(best):
                best = list(S)
                last = it
            outside = [v for v in range(n) if not inS[v]]
            if not outside:
                break
            mc = min(conf[v] for v in outside)
            add(rng.choice([v for v in outside if conf[v] == mc]))
            continue
        if it - last > 4000:
            # Stagnation: return to the best set, then drop a few random vertices.
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            for v in rng.sample(best, min(3, len(best))):
                remove(v)
            last = it
            continue
        conflicted = [u for u in S if conf[u] > 0]
        ok = [u for u in conflicted if tout[u] <= it] or conflicted
        mc = max(conf[u] for u in ok)
        u = rng.choice([x for x in ok if conf[x] == mc])
        remove(u)
        tin[u] = it + 7 + rng.randrange(10)
        outside = [v for v in range(n) if not inS[v] and tin[v] <= it]
        if not outside:
            outside = [v for v in range(n) if not inS[v]]
        if not outside:
            break
        mc = min(conf[v] for v in outside)
        v = rng.choice([x for x in outside if conf[x] == mc])
        add(v)
        tout[v] = it + 7 + rng.randrange(10)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a point twin v_p for each p in I, where I is a partial ovoid (pairwise
#     non-collinear points), adjacent to all lines through p;
#   * a line twin w_L for each L in J, where J is a partial spread (pairwise
#     disjoint lines), adjacent to all points of L.
# Point and line constraints are independent, so J is taken as a full regular
# spread (q^2+1 lines) and I is found by tabu search.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    pts, pidx = _w_points(q)
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    lidx = {tuple(ls): j for j, ls in enumerate(lines)}
    J = []
    try:
        sp = _regular_spread(q, pidx)
        cand = [lidx[tuple(s)] for s in sp if tuple(s) in lidx]
        covered = set()
        for j in cand:
            covered.update(lines[j])
        if len(cand) == q * q + 1 and len(covered) == P:
            J = cand
    except Exception:
        J = []
    now = time.monotonic()
    if not J:
        # Fallback if the explicit spread is unavailable.
        J = _tabu_is(L, [sorted(s) for s in ladj], now + 0.3 * (deadline - now), rng)
    I = _tabu_is(P, [sorted(s) for s in padj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2): degree d, diameter 4, with explicit spread lines.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
