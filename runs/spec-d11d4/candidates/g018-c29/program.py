import itertools
import random
import time

import lib


class _Abort(Exception):
    pass


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and totally isotropic lines.
# ----------------------------------------------------------------------------

def _gq_lines(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each t.i. line as a sorted point list."""
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
            Ls = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        Ls.add(index[norm(v)])
            Ls = sorted(Ls)
            lines.append(Ls)
            for p in Ls:
                cp = covered[p]
                for r in Ls:
                    cp[r] = 1
    return P, lines


# ----------------------------------------------------------------------------
# Regular-ish spread search: exact cover of points by pairwise disjoint lines,
# via DFS with minimum-remaining-options branching and random restarts.
# ----------------------------------------------------------------------------

def _spread(P, lines, q, rng, deadline):
    """Return a list of line indices forming a spread (each point covered once), or None."""
    need = q * q + 1
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    while time.monotonic() < deadline:
        blocked = [False] * P
        lblock = [0] * L
        chosen = []
        nodes = [0]
        limit = 4000

        def pick(j):
            for p in lines[j]:
                blocked[p] = True
                for j2 in pl[p]:
                    lblock[j2] += 1
            chosen.append(j)

        def unpick(j):
            chosen.pop()
            for p in lines[j]:
                blocked[p] = False
                for j2 in pl[p]:
                    lblock[j2] -= 1

        def dfs():
            if len(chosen) == need:
                return True
            nodes[0] += 1
            if nodes[0] > limit or time.monotonic() > deadline:
                raise _Abort
            bo = None
            for p in range(P):
                if not blocked[p]:
                    opts = [j for j in pl[p] if lblock[j] == 0]
                    if not opts:
                        return False
                    if bo is None or len(opts) < len(bo):
                        bo = opts
                        if len(opts) == 1:
                            break
            if bo is None:
                return len(chosen) == need
            rng.shuffle(bo)
            for j in bo:
                pick(j)
                if dfs():
                    return True
                unpick(j)
            return False

        try:
            ok = dfs()
        except _Abort:
            ok = False
        if ok:
            return list(chosen)
    return None


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists)."""
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
# Twin blow-up: replace each vertex in S by two copies with the same
# neighbourhood. Valid when every base vertex has at most one neighbour in S
# and base degree is d-1; then degrees stay <= d and diameter/bipartiteness
# are preserved.
# ----------------------------------------------------------------------------

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

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    # Projective plane incidence graph (degree d, diameter 3).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # W(d-1) incidence graph (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            P, lines = _gq_lines(d - 1)
            consider(P + len(lines),
                     [(p, P + j) for j, Ls in enumerate(lines) for p in Ls])
        except Exception:
            pass

    # Blow-up of W(q), q = d-2 (base degree q+1 = d-1; result degree d, diameter 4).
    q = d - 2
    if D >= 4 and 2 <= q <= 11 and lib.is_prime_power(q):
        try:
            P, lines = _gq_lines(q)
            L = len(lines)
            edges0 = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(P + L, edges0)

            # Lines: a spread (each point on exactly one blown line).
            S = []
            sp = _spread(P, lines, q, rng, t0 + 0.4 * budget)
            if sp:
                S += [P + j for j in sp]

            # Points: a partial ovoid (no two collinear, so each line has <= 1 blown point).
            padj = [set() for _ in range(P)]
            for Ls in lines:
                for p in Ls:
                    for r in Ls:
                        if p != r:
                            padj[p].add(r)
            O = _mis(P, [sorted(s) for s in padj], deadline, rng)
            S += O

            n, e = _blow(P + L, edges0, S)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
