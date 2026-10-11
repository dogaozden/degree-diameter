import itertools
import random
import sys
import time

import lib

sys.setrecursionlimit(20000)


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
# Tabu search for a large independent set (pure Python).
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
# Exact-style packing: choose candidates whose item-bitmasks are pairwise
# disjoint, maximizing the count. Randomized branch and bound with restarts.
# With candidates = lines (items = points) and masks = points on each line,
# a full packing is a spread of W(q) (q^2+1 lines). Candidates = points with
# items = lines gives a partial ovoid.
# ----------------------------------------------------------------------------

class _Stop(Exception):
    pass


def _pack_run(cmask, item_c, nitems, K, deadline, rng, node_limit):
    best = []
    count = [0]

    def rec(used, dead, chosen):
        nonlocal best
        if len(chosen) > len(best):
            best = list(chosen)
        count[0] += 1
        if count[0] > node_limit:
            raise _Stop()
        if (count[0] & 15) == 0 and time.monotonic() > deadline:
            raise _Stop()
        blocked = used | dead
        free = nitems - blocked.bit_count()
        if len(chosen) + free // K <= len(best):
            return
        zero = 0
        pick = -1
        pick_av = None
        for i in range(nitems):
            if (blocked >> i) & 1:
                continue
            av = [c for c in item_c[i] if not (cmask[c] & blocked)]
            if not av:
                zero |= 1 << i
            elif pick_av is None or len(av) < len(pick_av):
                pick = i
                pick_av = av
        if zero:
            rec(used, dead | zero, chosen)
            return
        if pick_av is None:
            return
        rng.shuffle(pick_av)
        for c in pick_av:
            rec(used | cmask[c], dead, chosen + [c])
        rec(used, dead | (1 << pick), chosen)

    try:
        rec(0, 0, [])
    except _Stop:
        pass
    return best


def _pack(cmask, nitems, deadline, rng, node_limit=3000):
    item_c = [[] for _ in range(nitems)]
    for c, m in enumerate(cmask):
        x = m
        while x:
            low = x & -x
            item_c[low.bit_length() - 1].append(c)
            x ^= low
    K = max(1, min(m.bit_count() for m in cmask))
    best = []
    while time.monotonic() < deadline:
        res = _pack_run(cmask, item_c, nitems, K, deadline, rng, node_limit)
        if len(res) > len(best):
            best = res
        if len(best) * K >= nitems:
            break
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# A partial spread J of lines (pairwise disjoint) and a partial ovoid I of
# points (pairwise non-collinear) are chosen. For each L in J add a line twin
# adjacent to the q+1 points of L; for each p in I add a point twin adjacent
# to the q+1 lines through p. Every old vertex gets at most one twin
# neighbour, so degrees stay <= q+2. A full spread (q^2+1 lines) is the
# largest J possible, and the twins keep all pairwise distances <= 4.
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

    line_mask = [sum(1 << p for p in Ls) for Ls in lines]   # items = points
    pt_mask = [sum(1 << j for j in pl[p]) for p in range(P)]  # items = lines

    now = time.monotonic()
    B = max(0.0, deadline - now)

    # Lines: pairwise disjoint (spread). Exact search first, then tabu.
    J = _pack(line_mask, P, now + 0.30 * B, rng)
    if len(J) * (q + 1) < P:
        Jm = _mis(L, [sorted(s) for s in ladj],
                  max(now + 0.40 * B, time.monotonic() + 0.1), rng)
        if len(Jm) > len(J):
            J = Jm

    # Points: pairwise non-collinear (partial ovoid). Exact search, then tabu.
    I = _pack(pt_mask, L, max(now + 0.60 * B, time.monotonic() + 0.1), rng)
    Im = _mis(P, [sorted(s) for s in padj],
              max(deadline, time.monotonic() + 0.1), rng)
    if len(Im) > len(I):
        I = Im

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
    budget = max(1.0, min(0.7 * time_limit, time_limit - 12.0))
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

    # W(d-2) with spread/ovoid twins using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
