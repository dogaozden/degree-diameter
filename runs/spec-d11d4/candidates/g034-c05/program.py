import itertools
import random
import time

import numpy as np

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
# Point twins for a pairwise non-collinear set I of points; line twins for a
# pairwise disjoint set J of lines. Both keep every pair within distance 4.
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
# Randomized greedy set-cover vertex extension for diameter 4, vectorized with
# numpy bitsets. A new vertex x joined to S (spare-degree vertices on one side)
# keeps diameter <= 4 when the union of ball3(s) over s in S covers all vertices.
# ----------------------------------------------------------------------------

NOISE = 0.25
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _popc_rows(A):
    """Popcount of each row of a 2-D uint64 array."""
    return _POP8[A.view(np.uint8)].sum(axis=1)


def _pick(pool, R, unc, rng):
    """Choose the next cover vertex from pool (numpy int array): best gain, or random useful with prob NOISE."""
    g = _popc_rows(R[pool] & unc)
    if rng.random() < NOISE:
        useful = pool[g > 0]
        if useful.size == 0:
            return -1
        return int(useful[rng.randrange(useful.size)])
    i = int(np.argmax(g))
    if g[i] == 0:
        return -1
    return int(pool[i])


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

    total_spare = sum(d - len(a) for a in adj)
    cap = n + total_spare // 2 + 2  # each new vertex uses at least 2 spare slots
    W = (cap + 63) // 64

    src = []
    dst = []
    for u, v in edges:
        src.append(u)
        dst.append(v)
        src.append(v)
        dst.append(u)

    def ball3(m):
        """Bitset per vertex (rows 0..m-1) of all vertices within distance 3."""
        idx = np.arange(m, dtype=np.int64)
        R0 = np.zeros((m, W), dtype=np.uint64)
        R0[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
        s = np.asarray(src, dtype=np.int64)
        t = np.asarray(dst, dtype=np.int64)
        R = R0
        if s.size == 0:
            return R
        order = np.argsort(s, kind="stable")
        s_sorted = s[order]
        t_sorted = t[order]
        starts = np.flatnonzero(np.concatenate(([True], s_sorted[1:] != s_sorted[:-1])))
        uniq = s_sorted[starts]
        for _ in range(3):
            agg = np.bitwise_or.reduceat(R[t_sorted], starts, axis=0)
            Rn = R.copy()
            Rn[uniq] |= agg
            R = Rn
        return R

    def full_mask(m):
        arr = np.zeros(W, dtype=np.uint64)
        for w in range(W):
            cnt = min(64, max(0, m - w * 64))
            if cnt == 64:
                arr[w] = np.uint64((1 << 64) - 1)
            elif cnt > 0:
                arr[w] = np.uint64((1 << cnt) - 1)
        return arr

    MAX_FAILS = 20000
    fails = 0
    R = None
    full = None
    dirty = True
    while time.monotonic() < deadline:
        if dirty:
            R = ball3(n)
            full = full_mask(n)
            dirty = False
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare or fails >= MAX_FAILS:
            break
        s0 = rng.choice(spare)
        pool = np.array([v for v in spare if color[v] == color[s0] and v != s0], dtype=np.int64)
        S = [s0]
        unc = full & ~R[s0]
        while unc.any() and len(S) < d and pool.size:
            bv = _pick(pool, R, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc = unc & ~R[bv]
            pool = pool[pool != bv]
        if unc.any():
            fails += 1
            continue
        x = n
        n += 1
        for s in S:
            edges.append((s, x))
            adj[s].append(x)
            src.append(s)
            dst.append(x)
            src.append(x)
            dst.append(s)
        adj.append(list(S))
        color.append(1 - color[s0])
        fails = 0
        dirty = True
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

    # Twin graph on W(d-2) (degree d), then several randomized set-cover
    # extensions using the spare slots; keep the largest valid result.
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
