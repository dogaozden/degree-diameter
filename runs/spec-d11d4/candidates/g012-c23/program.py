import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Field tables, nonsquare search, and the symplectic form that defines W(q).
# For odd q, the form is Tr_{GF(q^2)/GF(q)}(det) on GF(q^2)^2 = GF(q)^4, where
# GF(q^2) = GF(q)[t]/(t^2 - n) and n is a nonsquare. Every GF(q^2)-line is then
# totally isotropic, so the Desarguesian spread of PG(3,q) is a spread of W(q).
# ----------------------------------------------------------------------------

def _tables(q):
    F = lib.GF(q)
    add = F.add_table.tolist()
    mul = F.mul_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    return add, mul, neg, inv


def _nonsquare(q, mul):
    squares = {mul[a][a] for a in range(1, q)}
    return next(b for b in range(1, q) if b not in squares)


def _symplectic(q, add, mul, neg):
    if q % 2 == 0:
        def om(x, y):
            t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
            u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
            return add[t][u]
        return om
    n = _nonsquare(q, mul)

    def om(x, y):
        # x = (A, B) with A = x0 + x1*t, B = x2 + x3*t, t^2 = n.
        # omega = Re(A*B' - B*A'), which is alternating and nondegenerate.
        re_ab = add[mul[x[0]][y[2]]][mul[n][mul[x[1]][y[3]]]]
        re_ba = add[mul[x[2]][y[0]]][mul[n][mul[x[3]][y[1]]]]
        return add[re_ab][neg[re_ba]]
    return om


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list, plus (for odd q) the
# spread of W(q) coming from the GF(q^2)-lines (helper: _spread).
# ----------------------------------------------------------------------------

def _spread(q, pts, index, norm, add, mul, n, lines):
    """Spread of W(q) from GF(q^2)-lines: {GF(q^2)*v} for each point v. Returns line indices or None."""
    line_id = {Ls: k for k, Ls in enumerate(lines)}
    P = len(pts)
    seen = [False] * P
    out = []
    for v0 in range(P):
        if seen[v0]:
            continue
        v = pts[v0]
        u = (mul[n][v[1]], v[0], mul[n][v[3]], v[2])   # u = t * v
        Sset = set()
        for a in range(q):
            av = [mul[a][c] for c in v]
            for b in range(q):
                if a == 0 and b == 0:
                    continue
                w = tuple(add[av[k]][mul[b][u[k]]] for k in range(4))
                if any(w):
                    Sset.add(index[norm(w)])
        Ss = tuple(sorted(Sset))
        if Ss not in line_id:
            return None
        for p in Ss:
            seen[p] = True
        out.append(line_id[Ss])
    return out if len(out) == q * q + 1 else None


def _gq(q):
    """Return (P, lines, spread): points 0..P-1, totally isotropic lines (sorted point tuples), spread or None."""
    add, mul, neg, inv = _tables(q)
    om = _symplectic(q, add, mul, neg)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        ic = inv[next(c for c in v if c)]
        return tuple(mul[ic][c] for c in v)

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if i * P + j in covered:
                continue
            y = pts[j]
            if om(x, y) != 0:
                continue
            Lset = set()
            for a in range(q):
                ax = [mul[a][c] for c in x]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[ax[k]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = tuple(sorted(Lset))
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)

    spread = None
    if q % 2 == 1:
        spread = _spread(q, pts, index, norm, add, mul, _nonsquare(q, mul), lines)
    return P, lines, spread


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), degree q+1, diameter 4."""
    P, lines, _ = _gq(q)
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
# Point twins v_p (p in I, I pairwise non-collinear) attach to all lines through p.
# Line twins w_L (L in J, J pairwise disjoint) attach to all points of L.
# New idea: for odd q, J is a full spread of W(q) (q^2+1 lines) built algebraically
# from GF(q^2)-lines, so J is maximum-size and needs no search. Only I is searched.
# Every point then has degree q+2 (10 W-neighbours + one line twin), and each
# line has at most one point twin, so all degrees stay <= q+2.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines, spread = _gq(q)
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
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    if spread is not None:
        J = list(spread)
        I = _mis(P, [sorted(s) for s in padj], deadline, rng)
    else:
        now = time.monotonic()
        mid = now + (deadline - now) / 2.0
        I = _mis(P, [sorted(s) for s in padj], mid, rng)
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
    budget = max(1.0, min(0.75 * time_limit, time_limit - 12.0))
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

    # W(d-2) with point and line twins using the spare slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
