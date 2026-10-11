import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (pure Python), cached per q.
# ----------------------------------------------------------------------------

_GQ_CACHE = {}


def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    if q in _GQ_CACHE:
        return _GQ_CACHE[q]
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
    _GQ_CACHE[q] = (P, lines)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# NEW: iterated local search for maximum independent sets (ARW-style):
# (1,2)-swaps plus random forced insertions, with restore-to-best.
# ----------------------------------------------------------------------------

def _ils_mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n <= 0:
        return []
    adjset = [set(a) for a in adj]
    inS = [False] * n
    tight = [0] * n          # number of solution neighbours of each vertex
    cnt = [0]

    def ins(v):
        inS[v] = True
        cnt[0] += 1
        for w in adj[v]:
            tight[w] += 1

    def rem(v):
        inS[v] = False
        cnt[0] -= 1
        for w in adj[v]:
            tight[w] -= 1

    def fill():
        free = [v for v in range(n) if not inS[v] and tight[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tight[v] == 0:
                ins(v)

    def two_improve():
        improved = True
        while improved:
            if time.monotonic() > deadline:
                return
            improved = False
            xs = [v for v in range(n) if inS[v]]
            rng.shuffle(xs)
            for x in xs:
                if not inS[x]:
                    continue
                cand = [u for u in adj[x] if tight[u] == 1]
                if len(cand) < 2:
                    continue
                pair = None
                for i in range(len(cand)):
                    a = cand[i]
                    for j in range(i + 1, len(cand)):
                        b = cand[j]
                        if b not in adjset[a]:
                            pair = (a, b)
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    rem(x)
                    ins(pair[0])
                    ins(pair[1])
                    fill()
                    improved = True

    fill()
    two_improve()
    best = [v for v in range(n) if inS[v]]
    cur_best = len(best)
    while time.monotonic() < deadline:
        v = rng.randrange(n)
        tries = 0
        while (inS[v] or tight[v] > 2) and tries < 30:
            v = rng.randrange(n)
            tries += 1
        if inS[v]:
            continue
        for w in adj[v]:
            if inS[w]:
                rem(w)
        ins(v)
        fill()
        two_improve()
        if cnt[0] > cur_best:
            cur_best = cnt[0]
            best = [u for u in range(n) if inS[u]]
        elif cnt[0] < cur_best - 1:
            for u in range(n):
                if inS[u]:
                    rem(u)
            for u in best:
                ins(u)
    return best


# ----------------------------------------------------------------------------
# NEW: spread of W(q) by randomized exact-cover DFS with minimum-remaining-
# values branching and incremental availability counts. A spread is a set of
# pairwise disjoint lines covering all points: it gives q^2+1 line twins.
# ----------------------------------------------------------------------------

def _spread(P, lines, pl, k, deadline, rng):
    """Return a list of pairwise disjoint line indices, as large as found before deadline (a full spread if possible)."""
    L = len(lines)
    target = P // k
    alive = [True] * L
    avail = [len(pl[p]) for p in range(P)]
    uncovered = [True] * P
    chosen = []
    best_box = [[]]
    state = {"nodes": 0, "abort": False}
    limit = [20000]
    perm = list(range(P))

    def dfs():
        if len(chosen) > len(best_box[0]):
            best_box[0] = list(chosen)
        if len(chosen) == target:
            return True
        if state["abort"]:
            return False
        if state["nodes"] > limit[0] or time.monotonic() > deadline:
            state["abort"] = True
            return False
        bp = -1
        bv = 1 << 30
        for p in perm:
            if uncovered[p] and avail[p] < bv:
                bv = avail[p]
                bp = p
                if bv == 0:
                    break
        if bp < 0 or bv == 0:
            return False
        cands = [M for M in pl[bp] if alive[M]]
        rng.shuffle(cands)
        for M in cands:
            state["nodes"] += 1
            killed = []
            for x in lines[M]:
                for K in pl[x]:
                    if alive[K]:
                        alive[K] = False
                        killed.append(K)
                        for y in lines[K]:
                            avail[y] -= 1
            for x in lines[M]:
                uncovered[x] = False
            chosen.append(M)
            if dfs():
                return True
            chosen.pop()
            for x in lines[M]:
                uncovered[x] = True
            for K in killed:
                alive[K] = True
                for y in lines[K]:
                    avail[y] += 1
            if state["abort"]:
                return False
        return False

    while time.monotonic() < deadline:
        perm = list(range(P))
        rng.shuffle(perm)
        alive[:] = [True] * L
        avail[:] = [len(pl[p]) for p in range(P)]
        uncovered[:] = [True] * P
        chosen.clear()
        state["nodes"] = 0
        state["abort"] = False
        if dfs():
            return list(chosen)
        if state["abort"]:
            break
    return list(best_box[0])


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot:
#   * point twin v_p for p in I (I pairwise non-collinear), adjacent to all
#     q+1 lines through p; each line gets at most one twin neighbour;
#   * line twin w_L for L in J (J pairwise disjoint lines), adjacent to all
#     q+1 points of L; each point gets at most one twin neighbour.
# I is an independent set of the collinearity graph (partial ovoid) and J an
# independent set of the line-meeting graph (partial spread). A spread of
# W(q) has q^2+1 lines, so J is usually complete; I is found by ILS.
# ----------------------------------------------------------------------------

def _twin_construct(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    k = len(lines[0])
    target = P // k
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
    padj_l = [sorted(s) for s in padj]
    ladj_l = [sorted(s) for s in ladj]

    now = time.monotonic()
    span = max(0.0, deadline - now)

    # Line twins: try an exact spread first, then a local-search fallback.
    J = _spread(P, lines, pl, k, now + 0.35 * span, rng)
    if len(J) < target:
        J2 = _ils_mis(L, ladj_l, now + 0.5 * span, rng)
        if len(J2) > len(J):
            J = J2

    # Point twins: partial ovoid by local search with the remaining time.
    I = _ils_mis(P, padj_l, deadline, rng)

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

    # Twin graph on W(d-2): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_construct(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
