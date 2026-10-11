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
# Helpers for set-cover vertex extension.
# A new vertex x joined to S (spare-degree vertices on one bipartition side)
# keeps diameter <= D when every vertex lies within distance D-1 of some s in S.
# For even D, pairs of new vertices are then also automatically within D by
# parity, so validity is inductive.
# ----------------------------------------------------------------------------

NOISE = 0.25
RUIN = 12


def _ball(n, adj, r):
    """Return per-vertex bitmasks of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


def _two_color(n, adj):
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


def _materialize(n0, base_edges, ext):
    """Build (n, edges) from a base graph and the list ext of neighbour lists of extension vertices."""
    edges = list(base_edges)
    for i, S in enumerate(ext):
        x = n0 + i
        for s in S:
            edges.append((s, x))
    return n0 + len(ext), edges


def _grow(n0, base_edges, ext, d, r, deadline, rng, tries=120):
    """Greedily append extension vertices to ext (in place); return how many were added."""
    n, edges = _materialize(n0, base_edges, ext)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _two_color(n, adj)
    added = 0
    while time.monotonic() < deadline:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        reach = _ball(n, adj, r)
        full = (1 << n) - 1
        placed = False
        for _ in range(tries):
            if time.monotonic() >= deadline:
                break
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                continue
            x = n
            n += 1
            for s in S:
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            ext.append(list(S))
            added += 1
            placed = True
            break
        if not placed:
            break
    return added


def _ils(n0, base_edges, ext, d, D, r, deadline, rng):
    """Ruin-and-recreate over the extension sequence.

    Ruin: truncate the extension to a prefix (mostly the last few vertices, sometimes a
    random cut). Recreate: regrow greedily with fresh randomness. Accept the trial if it
    is valid and at least as large (occasionally one smaller). Return the best ext list.
    """
    n_c, e_c = _materialize(n0, base_edges, ext)
    if not lib.is_valid(n_c, e_c, d, D):
        ext = []
        n_c = n0
    cur = list(ext)
    cur_n = n_c
    best, best_n = list(cur), cur_n
    while time.monotonic() < deadline:
        L = len(cur)
        if L == 0:
            cut = 0
        elif rng.random() < 0.7:
            cut = L - rng.randint(1, min(L, RUIN))
        else:
            cut = rng.randint(0, L - 1)
        trial = cur[:cut]
        _grow(n0, base_edges, trial, d, r, deadline, rng)
        n_t, e_t = _materialize(n0, base_edges, trial)
        if n_t >= cur_n or (n_t == cur_n - 1 and rng.random() < 0.15):
            if lib.is_valid(n_t, e_t, d, D):
                cur, cur_n = trial, n_t
                if cur_n > best_n:
                    best, best_n = list(cur), cur_n
    return best


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

    # Twin graph on W(d-2) (degree d-1 base), then ruin-and-recreate extension
    # over the spare slots for even D (where the parity argument applies).
    if D >= 4 and D % 2 == 0 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n0, base_edges = _twin_graph(d - 2, t0 + 0.30 * budget, rng)
            consider(n0, base_edges)
            r = D - 1
            ext = []
            _grow(n0, base_edges, ext, d, r, t0 + 0.42 * budget, rng)
            n1, e1 = _materialize(n0, base_edges, ext)
            consider(n1, e1)
            ext = _ils(n0, base_edges, ext, d, D, r, deadline, rng)
            n2, e2 = _materialize(n0, base_edges, ext)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
