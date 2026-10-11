import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base constructions.
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


def _symplectic_quadrangle(q):
    """Return (npts, lines, spread) for W(q) built from F_{q^2}^2, or None.

    lines are sorted lists of point ids; spread is a list of q^2+1 line ids that
    pairwise share no point.
    """
    Q = q * q
    F = lib.GF(Q)
    mul, add, sub = F.mul, F.add, F.sub
    subfield = [x for x in range(Q) if F.pow(x, q) == x]
    if len(subfield) != q:
        return None
    scal = [x for x in subfield if x]
    tr = [add(z, F.pow(z, q)) for z in range(Q)]
    delta = 1

    pid = [-1] * (Q * Q)
    reps = []
    for a in range(Q):
        for b in range(Q):
            if (a or b) and pid[a * Q + b] < 0:
                k = len(reps)
                reps.append((a, b))
                for l in scal:
                    pid[mul(l, a) * Q + mul(l, b)] = k
    npts = len(reps)
    if npts != (Q * Q - 1) // (q - 1):
        return None

    def collinear(x, y):
        det = sub(mul(x[0], y[1]), mul(x[1], y[0]))
        return tr[mul(delta, det)] == 0

    covered = [set() for _ in range(npts)]
    lines = []
    for i in range(npts):
        x = reps[i]
        for j in range(i + 1, npts):
            if j in covered[i]:
                continue
            y = reps[j]
            if not collinear(x, y):
                continue
            L = set()
            for a in subfield:
                ax0, ax1 = mul(a, x[0]), mul(a, x[1])
                for b in subfield:
                    if a == 0 and b == 0:
                        continue
                    v0 = add(ax0, mul(b, y[0]))
                    v1 = add(ax1, mul(b, y[1]))
                    L.add(pid[v0 * Q + v1])
            if len(L) != q + 1:
                return None
            for p in L:
                covered[p] |= L
            lines.append(sorted(L))

    pdeg = [0] * npts
    for L in lines:
        for p in L:
            pdeg[p] += 1
    if any(c != q + 1 for c in pdeg):
        return None

    line_idx = {frozenset(L): j for j, L in enumerate(lines)}
    spread = []
    for v0, v1 in [(1, t) for t in range(Q)] + [(0, 1)]:
        key = frozenset(pid[mul(l, v0) * Q + mul(l, v1)] for l in range(1, Q))
        j = line_idx.get(key)
        if j is None:
            return None
        spread.append(j)
    if len(set(spread)) != Q + 1:
        return None
    return npts, lines, spread


# ----------------------------------------------------------------------------
# Independent-set search and twin blow-ups.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    if N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    best_size = 0
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return int(np.argmin(score))

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            add(pick())
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            add(pick())
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


def _ovoid_search(npts, lines, rng, nprng, deadline):
    """Large partial ovoid of the points: pairwise non-collinear point set."""
    nb = [set() for _ in range(npts)]
    for L in lines:
        for p in L:
            nb[p].update(L)
    nbl = []
    for p in range(npts):
        s = nb[p]
        s.discard(p)
        nbl.append(sorted(s))
    return _independent_set(npts, nbl, rng, nprng, deadline)


def _side_search(V, cs, rng, nprng, deadline):
    """Large conflict-free subset of one side V, using local conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph."""
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
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


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


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1, searching each side separately."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]

    now = time.monotonic()
    total = max(0.0, deadline - now)
    S = []
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# Max independent set by tabu search, used for the twin construction on W(q).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph found before deadline."""
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


def _twin_graph(q, deadline, rng):
    """W(q) with a conflict-free set of points and lines blown up into twins."""
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
# Greedy set-cover vertex extension for diameter <= 4.
# A new vertex joined to a set S of spare-degree vertices on one side keeps
# diameter D (checked here for D = 4) when the 3-balls of S cover all vertices.
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
# Routes.
# ----------------------------------------------------------------------------

def _spread_route(q, d, deadline, rng, nprng, consider):
    """Blow up W(q): partial ovoid on points, exact spread on lines; then extend."""
    geo = _symplectic_quadrangle(q)
    if geo is None:
        return
    npts, lines, spread = geo
    n0 = npts + len(lines)
    edges0 = [(p, npts + j) for j, L in enumerate(lines) for p in L]
    consider(n0, edges0)
    now = time.monotonic()
    ov_dl = now + 0.6 * (deadline - now)
    O = _ovoid_search(npts, lines, rng, nprng, ov_dl)
    S = list(O) + [npts + j for j in spread]
    n, e = _blow(n0, edges0, S)
    consider(n, e)
    n2, e2 = _extend(n, e, d, deadline, rng)
    consider(n2, e2)


def _twin_route(q, d, deadline, rng, consider):
    """Twin blow-up of W(q) via tabu MIS on both sides; then extend."""
    now = time.monotonic()
    tw_dl = now + 0.5 * (deadline - now)
    n2, e2 = _twin_graph(q, tw_dl, rng)
    consider(n2, e2)
    n3, e3 = _extend(n2, e2, d, deadline, rng)
    consider(n3, e3)


def _haar_search(d, deadline, D, rng, consider):
    """Cyclic Haar-graph fallback: random connection sets over Z_m, increasing m."""
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            consider(*found)
            misses = 0
        else:
            misses += 1
        m += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Projective plane incidence (Moore-optimal for D = 3 when d-1 is a prime power).
    pg = _pg(d)
    if pg is not None:
        try:
            consider(pg[0], pg[1])
        except Exception:
            pass
    if D == 3 and lib.is_prime_power(d - 1):
        return best

    q = d - 2
    base_ok = 2 <= q <= 11 and lib.is_prime_power(q)

    # D = 3: blow up PG(2, q) with q = d-2 (degree q+1 = d-1).
    if D == 3 and base_ok and time.monotonic() < deadline - 2.0:
        try:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    # D >= 4: generalized quadrangle W(d-1) when d-1 is a prime power.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11 \
            and time.monotonic() < deadline - 2.0:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # D >= 4: two blow-up routes on W(d-2), each with a greedy extension.
    if D >= 4 and base_ok:
        now = time.monotonic()
        rem = deadline - now
        if rem > 3.0:
            try:
                _spread_route(q, d, now + 0.45 * rem, rng, nprng, consider)
            except Exception:
                pass
        if deadline - time.monotonic() > 3.0:
            try:
                _twin_route(q, d, deadline, rng, consider)
            except Exception:
                pass

    # Generic fallback when nothing beat K_{d,d}.
    if best[0] <= 2 * d and time.monotonic() < deadline:
        try:
            _haar_search(d, deadline, D, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
