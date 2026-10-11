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
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
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
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
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
# Ball bitmasks.
# ----------------------------------------------------------------------------

def _balls23(n, adj):
    """Return (ball2, ball3): per-vertex bitmasks of vertices within distance 2 and 3."""
    reach = [1 << v for v in range(n)]
    out2 = None
    for k in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
        if k == 1:
            out2 = reach
    return out2, reach


# ----------------------------------------------------------------------------
# Pair extension for diameter 4: insert two adjacent new vertices x, y with
# spare sets SX (opposite colour to x) and SY, chosen by a two-sided greedy
# set cover over distance-2 and distance-3 balls.
# ----------------------------------------------------------------------------

def _pair_attempt(poolX, poolY, reach2, reach3, full, d, rng, noise):
    """Greedy two-sided cover; return (SX, SY) covering everything, or None."""
    SX, SY = [], []
    uX, uY = full, full
    cx, cy = list(poolX), list(poolY)
    while uX or uY:
        capX = len(SX) < d - 1 and bool(cx)
        capY = len(SY) < d - 1 and bool(cy)
        if not capX and not capY:
            break
        cands = []
        if capX:
            for b in cx:
                g = (reach3[b] & uX).bit_count() + (reach2[b] & uY).bit_count()
                cands.append((g, 0, b))
        if capY:
            for a in cy:
                g = (reach3[a] & uY).bit_count() + (reach2[a] & uX).bit_count()
                cands.append((g, 1, a))
        best = max(c[0] for c in cands)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thr = max(1, int(best * 0.85))
            choices = [c for c in cands if c[0] >= thr]
        else:
            choices = [c for c in cands if c[0] == best]
        _, side, v = rng.choice(choices)
        if side == 0:
            SX.append(v)
            uX &= ~reach3[v]
            uY &= ~reach2[v]
            cx.remove(v)
        else:
            SY.append(v)
            uY &= ~reach3[v]
            uX &= ~reach2[v]
            cy.remove(v)
    if uX or uY:
        return None
    return SX, SY


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Single-vertex cover: S containing s0 plus up to d-1 pool vertices whose balls cover everything, or None."""
    S = [s0]
    unc = full & ~reach[s0]
    pool = [v for v in pool_all if v != s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            choices = [i for i, g in enumerate(gains) if g >= thresh]
            i = rng.choice(choices)
        else:
            top = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(top)
        bv = pool[i]
        S.append(bv)
        unc &= ~reach[bv]
        pool[i] = pool[-1]
        pool.pop()
    if unc:
        return None
    return S


def _pair_extend(n, edges, d, deadline, rng, max_fails):
    """Repeatedly insert a pair (or a single vertex as fallback) while keeping degree d and diameter 4."""
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

    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if len(spare) < 2:
            break
        cols = ([v for v in spare if color[v] == 0],
                [v for v in spare if color[v] == 1])
        r2, r3 = _balls23(n, adj)
        full = (1 << n) - 1

        opts = [c for c in (0, 1) if cols[c] and cols[1 - c]]
        if opts:
            c = rng.choice(opts)
            poolX = cols[1 - c]
            poolY = cols[c]
            res = None
            for attempt in range(4):
                noise = 0.0 if attempt == 0 else rng.choice([0.15, 0.3, 0.5])
                res = _pair_attempt(poolX, poolY, r2, r3, full, d, rng, noise)
                if res is not None:
                    break
            if res is not None:
                SX, SY = res
                x, y = n, n + 1
                n += 2
                adj.append([])
                adj.append([])
                for s in SX:
                    edges.append((s, x))
                    adj[s].append(x)
                for s in SY:
                    edges.append((s, y))
                    adj[s].append(y)
                edges.append((x, y))
                adj[x] = list(SX) + [y]
                adj[y] = list(SY) + [x]
                color.append(c)
                color.append(1 - c)
                fails = 0
                continue

        # Single-vertex fallback.
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_all, r3, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
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
    return n, edges


# ----------------------------------------------------------------------------
# NEW: ruin-and-recreate on the tail of an extension.
#
# Pair extension only ever appends vertices at the end of the labelling. So
# we can "ruin" a graph by truncating its last r vertices (dropping their
# edges), which frees spare degree on the surviving vertices, and then
# "recreate" by running pair extension again from the truncated graph with
# fresh randomness. A truncation can lengthen old-old paths, so each cut is
# checked with lib.is_valid and shallower cuts are tried if it fails. A
# recreated graph is accepted only when it is at least as large as the
# current one, which lets the walk drift across plateaus.
# ----------------------------------------------------------------------------

def _truncate(keep, edges):
    """Keep vertices 0..keep-1 and the edges among them."""
    return keep, [(u, v) for u, v in edges if u < keep and v < keep]


def _cut_valid(n, edges, span_max, d, D, rng):
    """Try a few tail cuts of size <= span_max; return a valid (n, edges) or None."""
    tries = (rng.randint(2, span_max), rng.randint(2, max(2, span_max // 3)), 2)
    for r in tries:
        keep = n - r
        tn, te = _truncate(keep, edges)
        if lib.is_valid(tn, te, d, D):
            return tn, te
    return None


def _ruin_recreate(base_n, start, d, D, deadline, rng):
    """Iterated ruin-and-recreate from start; return the largest valid (n, edges) seen."""
    cur_n, cur_e = start
    top_n, top_e = start
    while time.monotonic() < deadline - 0.5:
        span = min(80, cur_n - base_n)
        if span < 2:
            break
        cut = _cut_valid(cur_n, cur_e, span, d, D, rng)
        if cut is None:
            cur_n, cur_e = top_n, top_e
            continue
        tn, te = cut
        now = time.monotonic()
        run_end = min(deadline, now + max(0.3, (deadline - now) / 8.0))
        try:
            nn, ne = _pair_extend(tn, te, d, run_end, rng, 300)
        except Exception:
            cur_n, cur_e = top_n, top_e
            continue
        if nn >= cur_n and lib.is_valid(nn, ne, d, D):
            cur_n, cur_e = nn, ne
            if nn > top_n:
                top_n, top_e = nn, ne
    return top_n, top_e


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
            return True
        return False

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

    # Twin graph on W(d-2), then pair extension, then ruin-and-recreate.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            consider(*base)
            base_n = base[0]

            # Initial pair extension from the twin base.
            now = time.monotonic()
            run_end = now + 0.4 * (deadline - now)
            ext = base
            try:
                n3, e3 = _pair_extend(base[0], base[1], d, run_end, rng, 3000)
                if n3 > base_n and lib.is_valid(n3, e3, d, D):
                    ext = (n3, e3)
                    consider(n3, e3)
            except Exception:
                ext = base

            # Ruin-and-recreate for the remaining time.
            try:
                rn, re_ = _ruin_recreate(base_n, ext, d, D, deadline, rng)
                consider(rn, re_)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
