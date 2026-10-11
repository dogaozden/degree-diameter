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
    core = P + L
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges, core


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


def _extend(n, edges, d, deadline, rng, max_fails=20000):
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

    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= max_fails:
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
# Large-neighbourhood search (LNS) for diameter 4.
# ----------------------------------------------------------------------------

LNS_MAX_REMOVE = 3
LNS_FAILS = 300


def _lns(n, edges, core, d, D, deadline, rng, consider):
    """Run LNS until deadline; report every strict improvement through consider(n, edges)."""
    if not lib.is_valid(n, edges, d, D):
        return
    best_n = n
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        room = cur_n - core
        if room < 1:
            break
        k = rng.randint(1, min(LNS_MAX_REMOVE, room))
        R = set(rng.sample(range(core, cur_n), k))
        mp = {}
        for v in range(cur_n):
            if v not in R:
                mp[v] = len(mp)
        base_e = [(mp[u], mp[v]) for u, v in cur_e if u not in R and v not in R]
        base_n = len(mp)
        sub_deadline = min(deadline, time.monotonic() + 2.0)
        n2, e2 = _extend(base_n, base_e, d, sub_deadline, rng, max_fails=LNS_FAILS)
        if n2 < cur_n:
            continue
        if not lib.is_valid(n2, e2, d, D):
            continue
        if n2 > best_n:
            best_n = n2
            consider(n2, e2)
        if n2 > cur_n or rng.random() < 0.5:
            cur_n, cur_e = n2, e2


# ----------------------------------------------------------------------------
# Z_m-voltage lifts of small bipartite base graphs.
# ----------------------------------------------------------------------------

def _base_adj(k, m, perm, volt):
    """Adjacency of the base dart graph: adj[b] = list of (neighbour_base_id * m, voltage mod m)."""
    adj = [[] for _ in range(2 * k)]
    for i in range(len(perm)):
        pi, vi = perm[i], volt[i]
        for u in range(k):
            v = k + pi[u]
            t = vi[u]
            adj[u].append((v * m, t))
            adj[v].append((u * m, (-t) % m))
    return adj


def _lift_score(k, m, adj, D, limit):
    """Total number of (source, vertex) pairs not reached within D steps; stops early once above limit."""
    N = 2 * k * m
    total = 0
    for b0 in range(2 * k):
        seen = bytearray(N)
        s0 = b0 * m
        seen[s0] = 1
        frontier = [s0]
        reached = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                b = x // m
                g = x - b * m
                for bm, t in adj[b]:
                    y = bm + (g + t) % m
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
        if total > limit:
            return total
    return total


def _lift_edges(k, m, adj):
    """Return (n, edges) for the lift described by the base adjacency."""
    E = set()
    for u in range(k):
        for g in range(m):
            x = u * m + g
            for bm, t in adj[u]:
                y = bm + (g + t) % m
                E.add((x, y))
    return 2 * k * m, sorted(E)


def _lift_search(d, D, k, m, deadline, rng):
    """Hill-climb voltages/matchings for a valid lift on 2*k*m vertices; return (n, edges) or None."""

    def fresh():
        perm = [rng.sample(range(k), k) for _ in range(d)]
        volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
        return perm, volt

    perm, volt = fresh()
    cur = _lift_score(k, m, _base_adj(k, m, perm, volt), D, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 400:
            perm, volt = fresh()
            cur = _lift_score(k, m, _base_adj(k, m, perm, volt), D, 1 << 60)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(k)
        if rng.random() < 0.6:
            old = volt[i][u]
            volt[i][u] = rng.randrange(m)
            new = _lift_score(k, m, _base_adj(k, m, perm, volt), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
        else:
            u2 = rng.randrange(k)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = _lift_score(k, m, _base_adj(k, m, perm, volt), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
    return _lift_edges(k, m, _base_adj(k, m, perm, volt))


def _lift_phase(d, D, bn, deadline, rng, consider):
    """Repeatedly search for lifts of growing order above bn until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline and bn < moore:
        ks = [k for k in (2, 3, 4, 5, 6) if 2 * k * (bn // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        m = bn // (2 * k) + 1
        now = time.monotonic()
        slice_end = min(deadline, now + max(4.0, (deadline - now) / 4.0))
        res = _lift_search(d, D, k, m, slice_end, rng)
        if res is not None:
            n, edges = res
            if n > bn and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                bn = n
    return bn


# ----------------------------------------------------------------------------
# NEW: bi-Cayley (Haar-type) graphs over non-abelian groups for diameter 4.
#
# Vertices a_g and b_g for g in G (|G| = N). Edges a_g ~ b_{g s} for s in S, |S| = d.
# Left multiplication is an automorphism, so only BFS from a_e and b_e is needed:
# the graph has diameter <= 4 iff both balls of radius 4 cover all 2N vertices.
# Search: hill-climb over S to drive the number of unreached vertices to zero.
# ----------------------------------------------------------------------------

def _reach_count(N, T, S, Sinv, src_side, src):
    """Number of vertices (both sides) within distance 4 of the given source (side 0 = A, 1 = B)."""
    visA = bytearray(N)
    visB = bytearray(N)
    if src_side == 0:
        visA[src] = 1
    else:
        visB[src] = 1
    front = [src]
    cur = src_side
    for _ in range(4):
        nxt = []
        if cur == 0:
            for g in front:
                row = T[g]
                for s in S:
                    y = row[s]
                    if not visB[y]:
                        visB[y] = 1
                        nxt.append(y)
            cur = 1
        else:
            for x in front:
                row = T[x]
                for t in Sinv:
                    y = row[t]
                    if not visA[y]:
                        visA[y] = 1
                        nxt.append(y)
            cur = 0
        front = nxt
        if not front:
            break
    return sum(visA) + sum(visB)


def _unreached(N, T, S, Sinv):
    """Count of vertices not within distance 4 of a_e plus those not within distance 4 of b_e."""
    return (2 * N - _reach_count(N, T, S, Sinv, 0, 0)) + (2 * N - _reach_count(N, T, S, Sinv, 1, 0))


def _cayley_search(N, T, invl, d, deadline, rng):
    """Hill-climb a connection set S of size d in the group; return S with zero unreached, or None."""

    def unr(S):
        Sinv = [invl[s] for s in S]
        return _unreached(N, T, S, Sinv)

    S = rng.sample(range(N), d)
    cur = unr(S)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 300:
            S = rng.sample(range(N), d)
            cur = unr(S)
            stall = 0
            continue
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        new = unr(S2)
        if new <= cur:
            if new < cur:
                stall = 0
            S, cur = S2, new
    return S


def _groups(N, rng):
    """Candidate groups of order N: semidirect Z_m x| Z_k specs (nontrivial r), plus cyclic last."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        rng.shuffle(rs)
        for r in rs[:4]:
            out.append(("s", m, k, r))
    rng.shuffle(out)
    out.append(("c", N))
    return out


def _make_group(spec):
    """Return (order, mul, inv) for a group spec from _groups."""
    if spec[0] == "c":
        return lib.cyclic_group(spec[1])
    return lib.semidirect_group(spec[1], spec[2], spec[3])


def _cayley_phase(d, D, target_half, deadline, rng, consider):
    """Search bi-Cayley graphs with side N >= target_half (order 2N beats the current best)."""
    top = lib._moore_bound(d, D) // 2
    for N in range(max(target_half, 2), min(target_half + 4, top) + 1):
        for spec in _groups(N, rng):
            if time.monotonic() > deadline - 1.0:
                return
            order, mul, inv = _make_group(spec)
            if order != N:
                continue
            T = [[mul(x, y) for y in range(N)] for x in range(N)]
            invl = [inv(x) for x in range(N)]
            slice_end = min(deadline, time.monotonic() + 6.0)
            S = _cayley_search(N, T, invl, d, slice_end, rng)
            if S is not None:
                edges = [(g, N + T[g][s]) for g in range(N) for s in S]
                consider(2 * N, edges)
                return


# ----------------------------------------------------------------------------
# Legacy pipeline (parent construction), restructured to take an explicit deadline.
# ----------------------------------------------------------------------------

def _legacy(d, D, rng, deadline, get_best, consider):
    start = time.monotonic()
    span = max(0.0, deadline - start)
    twin_deadline = start + 0.6 * span
    parent_deadline = start + 0.8 * span

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

    ext = None
    core = None
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2, core_v = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
            ext = (n3, e3)
            core = core_v
        except Exception:
            ext = None
            core = None

    if D == 4 and ext is not None:
        try:
            _lns(ext[0], ext[1], core, d, D, deadline, rng, consider)
        except Exception:
            pass
    elif D >= 2 and d >= 2:
        try:
            _lift_phase(d, D, get_best(), deadline, rng, consider)
        except Exception:
            pass


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

    def get_best():
        return best[0]

    cayley_on = (D == 4 and d >= 4)
    legacy_deadline = t0 + 0.55 * budget if cayley_on else deadline

    try:
        _legacy(d, D, rng, legacy_deadline, get_best, consider)
    except Exception:
        pass

    # Bold new construction: bi-Cayley graphs over non-abelian groups, aiming above the current best.
    if cayley_on:
        try:
            target_half = get_best() // 2 + 1
            _cayley_phase(d, D, target_half, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
