import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line incidence graph (pure Python).
# Points 0..P-1, lines P..P+L-1. Degree q+1, diameter 4.
# ----------------------------------------------------------------------------

def _gq(q):
    """Return (n, edges) for the point-line incidence graph of the symplectic GQ W(q)."""
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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of a graph with n vertices and neighbour lists adj."""
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
# Twin blow-up of a base graph whose vertices all have degree d-1.
#
# Blowing up v into two copies with the same neighbourhood raises each neighbour
# u's degree by one. So the blown-up set S must have no two vertices with a
# common neighbour. For a bipartite base the two sides are independent of each
# other in this conflict relation, so we solve a maximum independent set on each
# side separately.
# ----------------------------------------------------------------------------

def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies with the same neighbourhood."""
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


def _side_mis(vs, cs, deadline, rng):
    """Maximum-ish independent set of the conflict graph restricted to the vertex list vs."""
    idx = {v: i for i, v in enumerate(vs)}
    ladj = [[idx[w] for w in cs[v] if w in idx] for v in vs]
    res = _mis(len(vs), ladj, deadline, rng)
    return [vs[i] for i in res]


def _blowup(n0, edges0, d, deadline, rng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None

    # Conflict sets: vertices sharing a common neighbour.
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)

    # Bipartition of the base graph.
    col = [-1] * n0
    for s in range(n0):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    sides = [[v for v in range(n0) if col[v] == 0],
             [v for v in range(n0) if col[v] == 1]]

    now = time.monotonic()
    total = max(0.0, deadline - now)
    S = []
    for k, vs in enumerate(sides):
        if not vs:
            continue
        dl = now + total * (k + 1) / 2.0
        S += _side_mis(vs, cs, dl, rng)
    return _blow(n0, edges0, S)


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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    # Projective plane of largest prime-power order q <= d-1 (degree q+1 <= d, diameter 3).
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            try:
                consider(*lib.projective_plane_incidence(q))
            except Exception:
                pass
            break

    # W(d-1): exact degree d, diameter 4 (only when D >= 4).
    if D >= 4 and 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
        try:
            consider(*_gq(d - 1))
        except Exception:
            pass

    # Blow-up routes: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        base = None
        try:
            if D >= 4:
                base = _gq(q)
            elif D == 3:
                base = lib.projective_plane_incidence(q)
        except Exception:
            base = None
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            try:
                res = _blowup(n0, e0, d, deadline, rng)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best

