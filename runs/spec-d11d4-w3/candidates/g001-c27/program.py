import itertools
import random
import sys
import time

import lib

sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q).

    Points are 0..P-1, lines are P..P+L-1. Every point lies on q+1 lines, every
    line has q+1 points, and the incidence graph has diameter 4.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2.
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# New construction: packing-based twin blow-up.
#
# Blowing up a vertex v of a base graph G (all degrees d-1) into twins (v, v')
# with the same neighbourhood raises the degree of each neighbour by one. A set
# S of vertices can be doubled iff no base vertex is adjacent to two members of
# S, i.e. the neighbourhoods of members of S are pairwise disjoint. Each colour
# class can be packed independently, because the neighbourhoods of a class lie
# entirely on the other side.
#
# For W(q): a packing of points by their line-neighbourhoods is a partial
# ovoid, and a packing of lines by their point-neighbourhoods is a partial
# spread. A full spread has q^2+1 lines, which is the optimum for that side.
#
# The packing is found by a randomised depth-first search with restarts. It
# branches on the open item with the fewest available candidates and skips items
# that no available candidate can still cover. This is an exact-cover style
# search, not the conflict-graph local search used previously.
# ----------------------------------------------------------------------------

def _max_packing(sets, n_items, deadline, rng):
    """Large family of candidates whose item-sets are pairwise disjoint.

    sets[c] lists the items of candidate c. Returns a list of candidate indices.
    """
    m = len(sets)
    cand = [c for c in range(m) if sets[c]]
    if not cand or n_items == 0:
        return []
    item_cands = [[] for _ in range(n_items)]
    for c in cand:
        for x in sets[c]:
            item_cands[x].append(c)
    ub = n_items // min(len(sets[c]) for c in cand)

    blocked = [0] * m      # number of used items inside candidate c
    used = [False] * n_items
    free = [0] * n_items   # number of available candidates containing item x
    chosen = []
    best = []
    state = {"nodes": 0, "cap": 0}

    def reset():
        for c in range(m):
            blocked[c] = 0
        for x in range(n_items):
            used[x] = False
            free[x] = len(item_cands[x])
        chosen.clear()

    def take(c):
        for y in sets[c]:
            used[y] = True
            for c2 in item_cands[y]:
                blocked[c2] += 1
                if blocked[c2] == 1:
                    for z in sets[c2]:
                        free[z] -= 1

    def untake(c):
        for y in sets[c]:
            used[y] = False
            for c2 in item_cands[y]:
                blocked[c2] -= 1
                if blocked[c2] == 0:
                    for z in sets[c2]:
                        free[z] += 1

    def rec():
        state["nodes"] += 1
        if len(chosen) > len(best):
            best[:] = chosen
        if (len(best) >= ub or state["nodes"] > state["cap"]
                or time.monotonic() >= deadline):
            return True
        bx, bf = -1, 1 << 30
        skipped = []
        for x in range(n_items):
            if used[x]:
                continue
            f = free[x]
            if f == 0:
                used[x] = True          # no available candidate can cover it
                skipped.append(x)
            elif f < bf or (f == bf and rng.random() < 0.3):
                bf, bx = f, x
        stop = False
        if bx >= 0:
            opts = [c for c in item_cands[bx] if blocked[c] == 0]
            rng.shuffle(opts)
            for c in opts:
                chosen.append(c)
                take(c)
                stop = rec()
                untake(c)
                chosen.pop()
                if stop:
                    break
        for x in skipped:
            used[x] = False
        return stop

    while time.monotonic() < deadline and len(best) < ub:
        reset()
        state["cap"] = state["nodes"] + 4000
        rec()
    return list(best)


def _sides(n0, adj):
    """Two-colour the base graph (it is bipartite); return the two colour classes."""
    color = [-1] * n0
    for s in range(n0):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    classes = [[], []]
    for v in range(n0):
        classes[max(color[v], 0)].append(v)
    return classes


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(n0, edges0, d, deadline, rng):
    """Twin blow-up of a base graph of degree d-1 by packings on each colour class."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None

    sides = [s for s in _sides(n0, adj) if s]
    S = []
    now = time.monotonic()
    span = max(0.0, deadline - now)
    for idx, side in enumerate(sides):
        # Items are the neighbours of side vertices (they lie on the other side).
        item_id = {}
        sets = []
        for v in side:
            s = []
            for w in adj[v]:
                if w not in item_id:
                    item_id[w] = len(item_id)
                s.append(item_id[w])
            sets.append(s)
        sub_deadline = now + span * (idx + 1) / len(sides)
        picked = _max_packing(sets, len(item_id), sub_deadline, rng)
        S.extend(side[i] for i in picked)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
