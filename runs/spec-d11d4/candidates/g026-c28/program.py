import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Parent pipeline (kept as the safe, proven route): W(q) incidence, twin graph
# on W(q-1), and randomized set-cover extension.
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


NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
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

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
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
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


def _parent(d, D, rng, t0, pbudget):
    """Original pipeline, given pbudget seconds from t0. Always returns a valid (n, edges)."""
    deadline = t0 + pbudget
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.35 * pbudget
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
    return best


# ----------------------------------------------------------------------------
# New construction: bi-Cayley / group lifts over non-cyclic groups.
# Fibers A_0..A_{a-1}, B_0..B_{a-1}, each a copy of a group G of order N.
# Dart (i, j, g) joins x in A_i to x*g in B_j. The group acts regularly on each
# fiber by left multiplication, so diameter <= D is checked by one BFS per
# fiber. Multiplicities are fixed so degrees stay <= d; darts are searched by
# simulated annealing on the number of unreached (fiber, vertex) pairs.
# ----------------------------------------------------------------------------

TARGET_N = 1775


def _groups(N):
    """Semidirect groups Z_m x|_r Z_k of order N with r >= 2 (non-abelian when r != 1)."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append(("sd", m, k, r))
    return out


def _pick_group(N, rng):
    gs = _groups(N)
    if gs and rng.random() < 0.85:
        return rng.choice(gs)
    return None  # cyclic Z_N


def _table(N, spec):
    """Multiplication table T[x, y] = x*y of the group with elements 0..N-1 (identity 0)."""
    x = np.arange(N, dtype=np.int64)
    if spec is None:
        return (x[:, None] + x[None, :]) % N
    _, m, k, r = spec
    A = x // k
    B = x % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    return ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k


def _random_mult(a, b, d, N, rng):
    """Random multiplicity matrix with row and column sums <= d."""
    M = [[0] * b for _ in range(a)]
    rows = [0] * a
    cols = [0] * b
    pairs = [(i, j) for i in range(a) for j in range(b)]
    changed = True
    while changed:
        changed = False
        rng.shuffle(pairs)
        for i, j in pairs:
            if rows[i] < d and cols[j] < d and M[i][j] < N:
                M[i][j] += 1
                rows[i] += 1
                cols[j] += 1
                changed = True
    return M


def _cost(dc, F, N, D):
    """Total number of (source fiber, vertex) pairs at distance > D from (source, identity)."""
    total = 0
    for src in range(F):
        reach = [np.zeros(N, dtype=bool) for _ in range(F)]
        reach[src][0] = True
        for _ in range(D):
            new = [r.copy() for r in reach]
            for i, jj, tg, tgi in dc:
                if reach[i].any():
                    new[jj][tg] |= reach[i]
                if reach[jj].any():
                    new[i][tgi] |= reach[jj]
            reach = new
        total += F * N - sum(int(r.sum()) for r in reach)
    return total


def _attempt(a, N, d, D, table, rng, end, max_iter):
    """Simulated annealing over dart group elements; return darts [(i, j, g)] with zero cost, else None."""
    F = 2 * a
    Tc = np.ascontiguousarray(table.T)  # Tc[g][x] = x*g
    inv = np.argmax(table == 0, axis=1).tolist()
    M = _random_mult(a, a, d, N, rng)
    darts = []
    used = {}
    for i in range(a):
        for j in range(a):
            if M[i][j]:
                gs = rng.sample(range(N), M[i][j])
                used[(i, j)] = set(gs)
                darts += [[i, j, g] for g in gs]
    if not darts:
        return None

    def mk(i, j, g):
        return (i, a + j, Tc[g], Tc[inv[g]])

    dc = [mk(i, j, g) for i, j, g in darts]
    cur = _cost(dc, F, N, D)
    it = 0
    while cur > 0 and it < max_iter and time.monotonic() < end:
        it += 1
        k = rng.randrange(len(darts))
        i, j, g = darts[k]
        ng = rng.randrange(N)
        if ng in used[(i, j)]:
            continue
        temp = 0.5 * (1.0 - it / max_iter) + 0.02
        used[(i, j)].discard(g)
        used[(i, j)].add(ng)
        old = dc[k]
        dc[k] = mk(i, j, ng)
        new_cost = _cost(dc, F, N, D)
        if new_cost <= cur or rng.random() < math.exp(-(new_cost - cur) / temp):
            cur = new_cost
            darts[k] = [i, j, ng]
        else:
            dc[k] = old
            used[(i, j)].discard(ng)
            used[(i, j)].add(g)
    if cur == 0:
        return darts
    return None


def _edges(a, N, table, darts):
    edges = []
    for i, j, g in darts:
        col = table[:, g].tolist()
        base_a = i * N
        base_b = (a + j) * N
        edges.extend((base_a + x, base_b + col[x]) for x in range(N))
    return 2 * a * N, edges


def _search(d, D, rng, end):
    """Search group lifts for a valid graph with more than TARGET_N vertices; return best (n, edges) or None."""
    best = None
    bestn = 0
    state = {}
    for a in (3, 4, 2):
        state[a] = {"N": -(-TARGET_N // (2 * a)), "fails": 0}
    active = [3, 4, 2]
    slice_len = 8.0
    max_iter = 2500
    while active and time.monotonic() < end - 0.5:
        for a in list(active):
            if time.monotonic() >= end - 0.5:
                break
            st = state[a]
            N = st["N"]
            spec = _pick_group(N, rng)
            table = _table(N, spec)
            sl = min(end - 0.5, time.monotonic() + slice_len)
            darts = _attempt(a, N, d, D, table, rng, sl, max_iter)
            if darts is not None:
                n, edges = _edges(a, N, table, darts)
                if n > bestn and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    bestn = n
                st["N"] = N + max(1, N // 200)
                st["fails"] = 0
            else:
                st["fails"] += 1
                if st["fails"] >= 3:
                    active.remove(a)
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    if d == 11 and D == 4:
        # Half the budget to the proven parent pipeline, the rest to group-lift search.
        best = _parent(d, D, rng, t0, 0.5 * budget)
        searched = _search(d, D, rng, t0 + budget)
        if searched is not None and searched[0] > best[0] and lib.is_valid(searched[0], searched[1], d, D):
            best = searched
    else:
        best = _parent(d, D, rng, t0, budget)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
