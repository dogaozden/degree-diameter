import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# Exact-cover search for a spread of W(q): a set of pairwise disjoint lines
# covering every point. Randomized DFS with the most-constrained-point rule
# and restarts under a node limit.
# ----------------------------------------------------------------------------

class _Stop(Exception):
    pass


def _spread(P, lines, pl, deadline, rng):
    """Return a list of pairwise disjoint lines covering all points, or [] if none found by deadline."""
    L = len(lines)
    k = len(lines[0])
    target = P // k
    meet = []
    for x in range(L):
        s = set()
        for p in lines[x]:
            s.update(pl[p])
        s.discard(x)
        meet.append(list(s))

    while time.monotonic() < deadline:
        avail = [True] * L
        covered = [False] * P
        chosen = []
        nodes = [0]
        limit = 3000

        def dfs():
            if len(chosen) == target:
                return True
            nodes[0] += 1
            if nodes[0] > limit:
                raise _Stop()
            if (nodes[0] & 31) == 0 and time.monotonic() >= deadline:
                raise _Stop()
            bc = None
            for p in range(P):
                if covered[p]:
                    continue
                cands = [x for x in pl[p] if avail[x]]
                if not cands:
                    return False
                if bc is None or len(cands) < len(bc):
                    bc = cands
                    if len(bc) == 1:
                        break
            rng.shuffle(bc)
            for x in bc:
                removed = [x]
                avail[x] = False
                for y in meet[x]:
                    if avail[y]:
                        avail[y] = False
                        removed.append(y)
                for p in lines[x]:
                    covered[p] = True
                chosen.append(x)
                if dfs():
                    return True
                chosen.pop()
                for p in lines[x]:
                    covered[p] = False
                for y in removed:
                    avail[y] = True
            return False

        try:
            if dfs():
                return list(chosen)
        except _Stop:
            pass
    return []


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a point twin for each p in I (I pairwise non-collinear), adjacent to all
#     lines through p;
#   * a line twin for each L in J (J pairwise disjoint lines), adjacent to all
#     points of L.
# I and J are chosen independently. J is preferably an exact spread
# (q^2+1 lines), otherwise a local-search independent set.
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
    ladj_l = [sorted(s) for s in ladj]
    padj_l = [sorted(s) for s in padj]

    target = P // (q + 1)
    now = time.monotonic()
    J = _spread(P, lines, pl, now + 0.45 * (deadline - now), rng)
    if len(J) < target:
        now = time.monotonic()
        J2 = _mis(L, ladj_l, now + 0.4 * (deadline - now), rng)
        if len(J2) > len(J):
            J = J2

    now = time.monotonic()
    I = _mis(P, padj_l, deadline, rng)

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
    budget = max(1.0, 0.8 * time_limit - 4.0)
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # W(d-1): degree d, diameter 4.
    if D >= 4 and 2 <= d - 1 <= 9 and lib.is_prime_power(d - 1):
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twins on W(d-2): degree d, diameter 4.
    q = d - 2
    if D >= 4 and 2 <= q <= 9 and lib.is_prime_power(q) and time.monotonic() < deadline - 3.0:
        try:
            consider(*_twin_graph(q, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
