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
    """Incidence graph of W(q): (n, edges), degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph found before deadline."""
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
# NEW: weighted set-cover extension with breakout weights and numpy gains.
#
# A new vertex x joined to a set S (all S on one side, spare slots, one colour)
# keeps the graph valid iff every existing vertex lies within distance D-1 of
# some member of S (then d(x, v) <= D). Pure greedy covering treats all
# uncovered vertices equally. Here each vertex carries a breakout weight that
# grows every time it stays uncovered after a failed attempt, so the cover
# keeps attacking the vertices that are hardest to reach. Gains are computed as
# one matrix-vector product over the radius-(D-1) ball matrix.
# ----------------------------------------------------------------------------

NOISE_W = 0.2
MAX_FAILS_W = 150


def _colors(n, adj):
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
    return color


def _ball(n, adj, R):
    """Per-vertex bitmask of all vertices within distance R."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _matrix(reach, n):
    """Convert per-vertex bitmasks to an n x n float32 0/1 matrix (row v = ball of v)."""
    nb = (n + 7) // 8
    buf = b"".join(r.to_bytes(nb, "little") for r in reach)
    bits = np.unpackbits(np.frombuffer(buf, dtype=np.uint8).reshape(n, nb),
                         axis=1, bitorder="little")
    return bits[:, :n].astype(np.float32)


def _wextend(n, edges, d, R, deadline, rng):
    """Repeatedly add valid vertices by weighted greedy cover; return (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _colors(n, adj)
    wts = np.ones(n, dtype=np.float32)
    new_edges = list(edges)
    fails = 0
    M = None
    while time.monotonic() < deadline:
        if M is None:
            M = _matrix(_ball(n, adj, R), n)
        spare = np.array([len(a) < d for a in adj], dtype=bool)
        spare_idx = np.flatnonzero(spare).tolist()
        if not spare_idx:
            break
        col = np.array(color, dtype=np.int8)
        s0 = rng.choice(spare_idx)
        pool = spare & (col == col[s0])
        pool[s0] = False
        unc = M[s0] == 0
        S = [s0]
        while unc.any() and len(S) < d:
            cand = np.flatnonzero(pool)
            if cand.size == 0:
                break
            gains = M @ (wts * unc)
            if rng.random() < NOISE_W:
                good = cand[gains[cand] > 0]
                if good.size == 0:
                    break
                v = int(rng.choice(good.tolist()))
            else:
                g = gains[cand]
                j = int(np.argmax(g))
                if g[j] <= 0:
                    break
                v = int(cand[j])
            S.append(v)
            pool[v] = False
            unc &= (M[v] == 0)
        if unc.any():
            fails += 1
            if fails > MAX_FAILS_W:
                break
            wts = wts + unc.astype(np.float32)
            continue
        x = n
        n += 1
        for s in S:
            adj[s].append(x)
            new_edges.append((s, x))
        adj.append(list(S))
        color.append(1 - int(col[s0]))
        wts = np.append(wts, np.float32(1.0))
        fails = 0
        M = None
    return n, new_edges


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
    moore = lib._moore_bound(d, D)

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
    if best[0] >= moore:
        return best

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2) (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.3 * budget, rng)
            consider(n2, e2)
        except Exception:
            pass
    if best[0] >= moore:
        return best

    # NEW: weighted breakout extension from the best base found so far.
    # Each run restarts from the same base with a fresh random stream.
    base_n, base_e = best
    R = D - 1
    no_gain = 0
    while time.monotonic() < deadline - 1.0 and no_gain < 3:
        try:
            n3, e3 = _wextend(base_n, base_e, d, R, deadline, rng)
        except Exception:
            break
        if n3 <= best[0]:
            no_gain += 1
        else:
            no_gain = 0
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
