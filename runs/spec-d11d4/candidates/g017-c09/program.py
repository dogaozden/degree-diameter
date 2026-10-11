import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as points and totally isotropic lines.
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


def _gq_incidence(P, lines):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
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
# Twin construction on W(q): each vertex has one spare slot when degree is q+1
# and d = q+2. Point twins hang on lines through an independent set of points;
# line twins hang on the points of a set of pairwise disjoint lines.
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
# NEW: dominating-cover augmentation.
#
# Given a valid bipartite graph of diameter D with spare degree, a new vertex x
# on side s0 can join any vertices s on the opposite side with spare degree.
# Old distances can only shrink when x is added, so x keeps every old pair
# within D as long as every old vertex v lies within distance D-1 of some
# chosen neighbour s. That is a greedy set-cover over the balls
# B_{D-1}(s), computed once with boolean matrix powers. Each accepted vertex is
# re-checked with lib.is_valid, which also covers pairs that involve new
# vertices.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    st.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _augment(n, edges, d, D, deadline):
    if D < 2 or n == 0:
        return n, list(edges)
    adj = lib.adjacency(n, edges)
    color = _two_color(n, adj)
    if color is None:
        return n, list(edges)

    M = np.zeros((n, n), dtype=np.float32)
    for u, v in edges:
        M[u, v] = 1.0
        M[v, u] = 1.0
    np.fill_diagonal(M, 1.0)
    ball = M.copy()
    for _ in range(D - 2):                 # ball = closed neighbourhood power, radius D-1
        ball = ((ball @ M) > 0).astype(np.float32)
    C = ball > 0
    del ball, M

    cur_n = n
    cur = list(edges)
    degl = [len(a) for a in adj]

    progress = True
    while progress and time.monotonic() < deadline:
        progress = False
        for s0 in (0, 1):
            if time.monotonic() >= deadline:
                break
            src_side = 1 - s0
            cand = [v for v in range(n) if color[v] == src_side and degl[v] < d]
            if not cand:
                continue
            cand_arr = np.array(cand)
            avail = np.ones(len(cand), dtype=bool)
            uncovered = np.ones(n, dtype=bool)
            chosen = []
            while len(chosen) < d and uncovered.any():
                gains = (C[cand_arr] & uncovered).sum(axis=1)
                gains[~avail] = 0
                j = int(np.argmax(gains))
                if gains[j] == 0:
                    break
                chosen.append(cand[j])
                avail[j] = False
                uncovered &= ~C[cand[j]]
            if not chosen or uncovered.any():
                continue
            trial = cur + [(v, cur_n) for v in chosen]
            if lib.is_valid(cur_n + 1, trial, d, D):
                cur = trial
                for v in chosen:
                    degl[v] += 1
                degl.append(len(chosen))
                cur_n += 1
                progress = True
    return cur_n, cur


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

    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    cands = []
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            cands.append(lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4:
        twin_q = d - 2
        for q in sorted({d - 1, d - 2}, reverse=True):
            if not (2 <= q <= 11 and lib.is_prime_power(q)):
                continue
            try:
                P, lines = _gq_w(q)
            except Exception:
                continue
            # Plain W(q): degree q+1 <= d, leaves spare slots for augmentation.
            try:
                cands.append(_gq_incidence(P, lines))
            except Exception:
                pass
            if q == twin_q:
                try:
                    tw_deadline = t0 + 0.55 * budget
                    cands.append(_twin_graph(P, lines, tw_deadline, rng))
                except Exception:
                    pass

    for idx, (cn, ce) in enumerate(cands):
        consider(cn, ce)
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(cands) - idx)
        try:
            an, ae = _augment(cn, ce, d, D, slice_end)
            consider(an, ae)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
