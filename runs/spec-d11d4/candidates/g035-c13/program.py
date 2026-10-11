import itertools
import math
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
# Randomized greedy set-cover vertex extension for diameter 4.
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

    spare = [v for v in range(n) if len(adj[v]) < d]

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
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
            spare = [v for v in spare if len(adj[v]) < d]
            if len(S) < d:
                spare.append(x)
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# NEW: voltage-lift search over small (semi)direct-product groups.
# Base: k vertices per side, d darts per base vertex (d permutations of range(k),
# each dart carrying a group voltage). Lift: A(i,x)~B(j,x*g) for each dart (i,j,g).
# Left translations are automorphisms, so diameter <= D iff the ball of radius D
# around A(i,e) and B(j,e) covers the whole lift, for every base vertex.
# ----------------------------------------------------------------------------

def _group_pick(G, rng, want):
    """Return up to `want` group specs of order G: (m, k2, r) semidirect products, or None for cyclic."""
    cands = []
    for m in range(3, G):
        if G % m:
            continue
        k2 = G // m
        if k2 < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1:
                cands.append((m, k2, r))
    rng.shuffle(cands)
    if not cands:
        return [None]
    return cands[:want - 1] + [None]


def _tables(G, spec):
    """Multiplication and inverse tables for the group of order G described by spec."""
    if spec is None:
        _, mul, inv = lib.cyclic_group(G)
    else:
        m, k2, r = spec
        _, mul, inv = lib.semidirect_group(m, k2, r)
    mt = [[mul(x, y) for y in range(G)] for x in range(G)]
    it = [inv(x) for x in range(G)]
    return mt, it


def _cost(k, G, d, D, mt, it, sig, volt):
    """Total number of (source, target) pairs not reached within distance D from the 2k base representatives."""
    N2 = k * G
    outA = [[] for _ in range(k)]
    inB = [[] for _ in range(k)]
    for t in range(d):
        st = sig[t]
        vt = volt[t]
        for i in range(k):
            j = st[i]
            g = vt[i]
            outA[i].append((j, g))
            inB[j].append((i, it[g]))
    total = 0
    for s in range(2 * k):
        seen = bytearray(2 * N2)
        src = s * G if s < k else N2 + (s - k) * G
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N2:
                    i, x = divmod(v, G)
                    row = mt[x]
                    for j, g in outA[i]:
                        w = N2 + j * G + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    j, y = divmod(v - N2, G)
                    row = mt[y]
                    for i, h in inB[j]:
                        w = i * G + row[h]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not nxt:
                break
        total += 2 * N2 - count
    return total


def _climb(k, G, d, D, mt, it, deadline, rng):
    """Hill-climb voltages/permutations until the lift has diameter <= D; return (sig, volt) or None."""
    sig = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cur = _cost(k, G, d, D, mt, it, sig, volt)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        t = rng.randrange(d)
        i = rng.randrange(k)
        if rng.random() < 0.6:
            old = volt[t][i]
            volt[t][i] = rng.randrange(G)
            new = _cost(k, G, d, D, mt, it, sig, volt)
            if new <= cur or rng.random() < 0.02:
                cur = new
            else:
                volt[t][i] = old
        else:
            i2 = rng.randrange(k)
            if i2 == i:
                continue
            sig[t][i], sig[t][i2] = sig[t][i2], sig[t][i]
            volt[t][i], volt[t][i2] = volt[t][i2], volt[t][i]
            new = _cost(k, G, d, D, mt, it, sig, volt)
            if new <= cur or rng.random() < 0.02:
                cur = new
            else:
                sig[t][i], sig[t][i2] = sig[t][i2], sig[t][i]
                volt[t][i], volt[t][i2] = volt[t][i2], volt[t][i]
    return sig, volt


def _build_lift(k, G, mt, sig, volt):
    """Materialize the lift as (n, edges)."""
    N2 = k * G
    edges = set()
    for t in range(len(sig)):
        for i in range(k):
            j = sig[t][i]
            g = volt[t][i]
            for x in range(G):
                edges.add((i * G + x, N2 + j * G + mt[x][g]))
    return 2 * N2, sorted(edges)


def _lift_search(d, D, deadline, rng, best_n, consider):
    """Search voltage lifts with order above best_n; pass each valid lift to consider()."""
    moore = lib._moore_bound(d, D)
    for k in (2, 3, 4):
        G = -(-(best_n + 1) // (2 * k))
        while time.monotonic() < deadline and 2 * k * G <= moore:
            found = None
            for spec in _group_pick(G, rng, 3):
                if time.monotonic() >= deadline:
                    break
                mt, it = _tables(G, spec)
                end = min(deadline, time.monotonic() + 4.0)
                res = _climb(k, G, d, D, mt, it, end, rng)
                if res is not None:
                    found = (mt, res)
                    break
            if found is None:
                break
            mt, (sig, volt) = found
            n, edges = _build_lift(k, G, mt, sig, volt)
            consider(n, edges)
            G += 1


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

    use_lift = (D >= 3 and d >= 6)
    pdeadline = t0 + (0.6 * budget if use_lift else budget)
    pbudget = pdeadline - t0

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

    # Twin graph on W(d-2) (degree d), then randomized set-cover extensions.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.35 * pbudget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= pdeadline - 0.5:
                    break
                slice_end = now + (pdeadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, pdeadline), rng)
                consider(n3, e3)
        except Exception:
            pass

    # Bold path: voltage lifts over small non-abelian groups, aiming above the current best.
    if use_lift and time.monotonic() < deadline:
        try:
            _lift_search(d, D, deadline, rng, best[0], consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
