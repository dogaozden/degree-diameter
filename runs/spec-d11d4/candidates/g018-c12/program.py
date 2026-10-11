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
# Maximum independent set by k-fixed tabu search (pure Python).
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
# Greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

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
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
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


# ----------------------------------------------------------------------------
# NEW: bipartite Z_m voltage lifts of a small d-regular base multigraph.
#
# Base graph: k "A" vertices and k "B" vertices. Its edge set is the union of
# d random perfect matchings (one permutation per layer), so it is d-regular.
# Each dart carries a voltage in Z_m. The lift has 2*k*m vertices, is bipartite
# and has degree <= d. Diameter 4 is checked by bitmask BFS over Z_m from one
# representative of each base vertex. The lift is translation-invariant, so
# these representatives cover all lifted vertices. A hill climb mutates voltages
# and layer permutations until every representative reaches all of Z_m in 4 steps.
# ----------------------------------------------------------------------------

def _rot(x, s, m, full):
    """Shift the m-bit cyclic mask x by s (x bit t moves to bit t+s mod m)."""
    s %= m
    if s == 0:
        return x
    return ((x << s) | (x >> (m - s))) & full


def _lift_cost(k, m, darts):
    """Total number of (base vertex, Z_m residue) pairs not reached within distance 4 from the 2k representatives."""
    full = (1 << m) - 1
    N = 2 * k
    fwd = [[] for _ in range(k)]
    bwd = [[] for _ in range(k)]
    for i, jb, g in darts:
        fwd[i].append((jb, g % m))
        bwd[jb].append((i, (-g) % m))
    total = 0
    for rep in range(N):
        reach = [0] * N
        reach[rep] = 1
        front = list(reach)
        for _ in range(4):
            new = [0] * N
            for i in range(k):
                f = front[i]
                if f:
                    for jb, s in fwd[i]:
                        new[k + jb] |= _rot(f, s, m, full)
            for jb in range(k):
                f = front[k + jb]
                if f:
                    for i, s in bwd[jb]:
                        new[i] |= _rot(f, s, m, full)
            for v in range(N):
                new[v] &= ~reach[v] & full
                reach[v] |= new[v]
            front = new
        total += sum(m - r.bit_count() for r in reach)
    return total


def _lift_climb(k, m, d, deadline, rng):
    """Hill-climb voltages and layer permutations; return darts (i, jb, g) with diameter <= 4, or None."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]

    def darts_of():
        return [(i, perms[t][i], volt[t][i]) for t in range(d) for i in range(k)]

    cur = _lift_cost(k, m, darts_of())
    stall = 0
    while cur > 0 and time.monotonic() < deadline:
        stall += 1
        if stall > 30000:
            perms = [rng.sample(range(k), k) for _ in range(d)]
            volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
            cur = _lift_cost(k, m, darts_of())
            stall = 0
            continue
        if rng.random() < 0.8 or k == 1:
            t = rng.randrange(d)
            i = rng.randrange(k)
            old = volt[t][i]
            volt[t][i] = rng.randrange(m)
            new = _lift_cost(k, m, darts_of())
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[t][i] = old
        else:
            t = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            perms[t][a], perms[t][b] = perms[t][b], perms[t][a]
            new = _lift_cost(k, m, darts_of())
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                perms[t][a], perms[t][b] = perms[t][b], perms[t][a]
    if cur == 0:
        return darts_of()
    return None


def _lift_search(d, deadline, rng, best_n, consider_fn):
    """Search voltage lifts with k = 2, then k = 3 base vertices per side, until deadline."""
    ks = (2, 3)
    for idx, k in enumerate(ks):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(ks) - idx)
        kdeadline = now + share
        m = max(2, best_n // (2 * k) + 1)
        while time.monotonic() < kdeadline:
            darts = _lift_climb(k, m, d, kdeadline, rng)
            if darts is None:
                break
            base_darts = [(i, k + jb, g) for i, jb, g in darts]
            n, edges = lib.voltage_lift(2 * k, base_darts, m)
            if n > best_n and lib.is_valid(n, edges, d, 4):
                consider_fn(n, edges)
                best_n = n
            m = max(m + 1, best_n // (2 * k) + 1)


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

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    # Parent pipeline gets about half the budget; the lift search gets the rest.
    parent_deadline = t0 + 0.5 * budget
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.25 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # New construction: Z_m voltage lifts of d-regular bipartite base graphs, diameter 4.
    if D == 4 and d >= 4 and time.monotonic() < deadline:
        try:
            _lift_search(d, deadline, rng, best[0],
                         lambda n, e: consider(n, e))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
