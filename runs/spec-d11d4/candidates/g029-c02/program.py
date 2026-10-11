import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

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
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
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
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
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
# Ball helpers for diameter 4.
# ----------------------------------------------------------------------------

def _balls23(n, adj):
    """Return (B2, B3): per-vertex bitmasks of vertices within distance 2 and within distance 3."""
    r = [1 << v for v in range(n)]
    out = []
    for _ in range(3):
        new = []
        for v in range(n):
            x = r[v]
            for u in adj[v]:
                x |= r[u]
            new.append(x)
        r = new
        out.append(r)
    return out[1], out[2]


# ----------------------------------------------------------------------------
# NEW: joint pair insertion.
# Two new vertices x (colour c) and y (colour 1-c) are added with edge x-y.
# x joins Sx (spare, colour 1-c, |Sx| <= d-1); y joins Sy (spare, colour c, |Sy| <= d-1).
# Both new vertices reach every old vertex within distance 4 iff
#   cover_x = OR_{s in Sx} B3[s] | OR_{t in Sy} B2[t] == full
#   cover_y = OR_{t in Sy} B3[t] | OR_{s in Sx} B2[s] == full
# This is exact: it uses paths x-y-t-..., and x-s-..., and adding vertices never
# lengthens old distances, so old pairs keep distance <= 4.
# ----------------------------------------------------------------------------

def _try_pair(color, spare, B2, B3, full, d, rng):
    """Greedily find (Sx, Sy) so the joint pair covers everything; return None on failure."""
    c = rng.randrange(2)
    PX = [v for v in spare if color[v] == 1 - c]
    PY = [v for v in spare if color[v] == c]
    if not PX or not PY:
        return None
    s0 = rng.choice(PX)
    t0 = rng.choice(PY)
    Sx = [s0]
    Sy = [t0]
    Cx = B3[s0] | B2[t0]
    Cy = B3[t0] | B2[s0]
    candX = [v for v in PX if v != s0]
    candY = [v for v in PY if v != t0]
    cap = d - 1
    while True:
        defx = full & ~Cx
        defy = full & ~Cy
        if not defx and not defy:
            return Sx, Sy
        canX = bool(defx) and len(Sx) < cap and bool(candX)
        canY = bool(defy) and len(Sy) < cap and bool(candY)
        if not canX and not canY:
            return None
        if canX and (not canY or defx.bit_count() >= defy.bit_count()):
            rng.shuffle(candX)
            best, bv = -1, -1
            for v in candX:
                g = (B3[v] & defx).bit_count() + (B2[v] & defy).bit_count()
                if g > best:
                    best, bv = g, v
            if best <= 0:
                return None
            Sx.append(bv)
            candX.remove(bv)
            Cx |= B3[bv]
            Cy |= B2[bv]
        else:
            rng.shuffle(candY)
            best, bv = -1, -1
            for v in candY:
                g = (B3[v] & defy).bit_count() + (B2[v] & defx).bit_count()
                if g > best:
                    best, bv = g, v
            if best <= 0:
                return None
            Sy.append(bv)
            candY.remove(bv)
            Cy |= B3[bv]
            Cx |= B2[bv]


NOISE = 0.25
PAIR_P = 0.5


def _pick(pool, reach, unc, rng):
    """Choose the next single-vertex cover element: best gain, or a random useful one with prob NOISE."""
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


def _extend(n, edges, d, deadline, rng):
    """Greedily add single vertices and joint pairs while keeping max degree d and diameter 4."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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

    spare = [v for v in range(n) if len(adj[v]) < d]

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        B2, reach = _balls23(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges

            if rng.random() < PAIR_P:
                res = _try_pair(color, spare, B2, reach, full, d, rng)
                if res is None:
                    fails += 1
                    continue
                Sx, Sy = res
                cx = 1 - color[Sx[0]]
                x = n
                y = n + 1
                n += 2
                color.append(cx)
                color.append(1 - cx)
                adj.append(list(Sx) + [y])
                adj.append(list(Sy) + [x])
                for s in Sx:
                    edges.append((s, x))
                    adj[s].append(x)
                for t in Sy:
                    edges.append((t, y))
                    adj[t].append(y)
                edges.append((x, y))
                spare = [v for v in spare if len(adj[v]) < d]
                if len(adj[x]) < d:
                    spare.append(x)
                if len(adj[y]) < d:
                    spare.append(y)
                fails = 0
                grown = True
                break

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
            spare = [v for v in spare if len(adj[v]) < d]
            if len(S) < d:
                spare.append(x)
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
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

    # Twin graph on W(d-2) (degree d), then randomized extensions mixing
    # single-vertex set-cover insertions with joint pair insertions.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.35 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= deadline - 0.5:
                    break
                slice_end = now + (deadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, deadline), rng)
                consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
