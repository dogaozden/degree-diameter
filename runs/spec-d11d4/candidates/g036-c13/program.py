import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangles as point/line lists (pure Python, table-based).
#   W(q): symplectic quadrangle, any prime power q.
#   Q(4,q): parabolic quadric quadrangle, q odd. Same parameters (q,q) as W(q)
#           but not isomorphic to it for odd q, so it is a genuinely different base.
# ----------------------------------------------------------------------------

def _tables(q):
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    return mul, add, neg, inv


def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    mul, add, neg, inv = _tables(q)
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


def _gq_q4(q):
    """Return (P, lines) for the parabolic quadric Q(4,q), q odd: singular points of x0x1+x2x3+x4^2."""
    if q % 2 == 0:
        raise ValueError("Q(4,q) construction here needs q odd")
    mul, add, neg, inv = _tables(q)

    def Qf(v):
        t = add[mul[v[0]][v[1]]][mul[v[2]][v[3]]]
        return add[t][mul[v[4]][v[4]]]

    def Bf(x, y):
        t = add[mul[x[0]][y[1]]][mul[x[1]][y[0]]]
        t = add[t][mul[x[2]][y[3]]]
        t = add[t][mul[x[3]][y[2]]]
        t = add[t][mul[x[4]][y[4]]]
        return add[t][mul[x[4]][y[4]]]  # 2 * x4 * y4

    pts = [v for v in itertools.product(range(q), repeat=5)
           if any(v) and next(c for c in v if c) == 1 and Qf(v) == 0]
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
            if Bf(x, y):
                continue  # not collinear in Q(4,q)
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(5))
                    if any(v):
                        t = index.get(norm(v))
                        if t is not None:
                            Lset.add(t)
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _incidence(P, lines):
    """Incidence graph of a point/line system: points 0..P-1, lines P..P+L-1."""
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
# Twin construction on a generalized quadrangle of order (q,q), degree q+2.
# Point twins for a pairwise non-collinear set I of points; line twins for a
# pairwise disjoint set J of lines. Both keep every pair within distance 4.
# ----------------------------------------------------------------------------

def _twin_graph(P, lines, deadline, rng):
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
# Randomized greedy set-cover vertex extension for diameter 4.
# A new vertex x joined to S (spare-degree vertices on one side) keeps
# diameter <= 4 when the union of ball3(s) over s in S covers all vertices.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
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
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
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
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
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

def _run_family(P, lines, d, rng, t_start, t_end, consider):
    """Twin graph on a GQ of order (d-2, d-2), then several set-cover extensions in [t_start, t_end]."""
    n2, e2 = _twin_graph(P, lines, t_start + 0.35 * (t_end - t_start), rng)
    consider(n2, e2)
    attempts = 3
    for a in range(attempts):
        now = time.monotonic()
        if now >= t_end - 0.5:
            break
        slice_end = now + (t_end - now) / (attempts - a)
        n3, e3 = _extend(n2, e2, d, min(slice_end, t_end), rng)
        consider(n3, e3)


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

    # Direct GQ incidence graphs of order (d-1, d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_incidence(*_gq_w(d - 1)))
        except Exception:
            pass
        if (d - 1) % 2 == 1 and d - 1 >= 3:
            try:
                consider(*_incidence(*_gq_q4(d - 1)))
            except Exception:
                pass

    # Families for the twin + extension pipeline on GQ(d-2, d-2).
    # Weighted time split: symplectic W(q) and parabolic Q(4,q) are different bases.
    fams = []
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        fams.append((_gq_w, 0.4))
        if (d - 2) % 2 == 1 and d - 2 >= 3:
            fams.append((_gq_q4, 0.6))

    for idx, (fn, _w) in enumerate(fams):
        now = time.monotonic()
        if now >= deadline - 0.5:
            break
        remaining_w = sum(w for _, w in fams[idx:])
        fend = min(deadline, now + (deadline - now) * _w / remaining_w)
        try:
            P, lines = fn(d - 2)
            _run_family(P, lines, d, rng, now, fend, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
