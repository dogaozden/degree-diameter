import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) with an explicit Desarguesian spread.
#
# Field K = GF(q^2) = GF(q)[x]/(x^2 + beta x + gamma), represented as pairs
# (u, v) meaning u + v x. The symplectic form on K^2 = GF(q)^4 is
#     g((a, b), (c, d)) = Tr(a*d - b*c),   Tr(u + v x) = 2u - beta*v.
# Its totally isotropic lines form W(q). The sets U_lambda = {(t, lambda t)}
# (lambda in K) together with U_inf = {(0, t)} are totally isotropic and
# partition the points, so they form a spread of W(q) with q^2 + 1 lines.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines, spread): W(q) points 0..P-1, totally isotropic lines as sorted point lists,
    and spread (list of line indices, or None if the explicit spread failed to match)."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    # x^2 + beta*x + gamma irreducible over GF(q): no root in GF(q).
    beta, gamma = next((b, g) for b in range(q) for g in range(q)
                       if all(add[add[mul[r][r]][mul[b][r]]][g] != 0 for r in range(q)))

    def kmul(a, c):
        a0, a1 = a
        c0, c1 = c
        const = add[mul[a0][c0]][neg[mul[mul[a1][c1]][gamma]]]
        xc = add[add[mul[a0][c1]][mul[a1][c0]]][neg[mul[mul[a1][c1]][beta]]]
        return (const, xc)

    def tr(z):
        u, v = z
        return add[add[u][u]][neg[mul[v][beta]]]

    def form(X, Y):
        a = (X[0], X[1])
        b = (X[2], X[3])
        c = (Y[0], Y[1])
        d = (Y[2], Y[3])
        return add[tr(kmul(a, d))][neg[tr(kmul(b, c))]]

    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

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

    # Explicit spread U_lambda (lambda in K) plus U_inf.
    lineid = {tuple(Ls): j for j, Ls in enumerate(lines)}
    spread = []
    ok = True
    for lam in [(l0, l1) for l0 in range(q) for l1 in range(q)] + [None]:
        Sset = set()
        for t0 in range(q):
            for t1 in range(q):
                if t0 == 0 and t1 == 0:
                    continue
                if lam is None:
                    X = (0, 0, t0, t1)
                else:
                    lt = kmul(lam, (t0, t1))
                    X = (t0, t1, lt[0], lt[1])
                Sset.add(index[norm(X)])
        j = lineid.get(tuple(sorted(Sset)))
        if j is None or len(Sset) != q + 1:
            ok = False
            break
        spread.append(j)
    if not ok or len(set(spread)) != len(spread):
        spread = None
    return P, lines, spread


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines, _ = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Point twins v_p (p in I, pairwise non-collinear) join all lines through p.
# Line twins w_L (L in J, pairwise disjoint) join all points of L.
# J is taken as the explicit spread (82 lines for q = 9), which is optimal;
# I is found by local search for a partial ovoid, using the remaining time.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines, spread = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)

    now = time.monotonic()
    if spread is not None:
        J = spread
        I = _mis(P, [sorted(s) for s in padj], deadline, rng)
    else:
        mid = now + (deadline - now) / 2.0
        I = _mis(P, [sorted(s) for s in padj], mid, rng)
        ladj = [set() for _ in range(L)]
        for p in range(P):
            for a in pl[p]:
                for b in pl[p]:
                    if a != b:
                        ladj[a].add(b)
        J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

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
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
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

    # Twins on W(d-2) using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
