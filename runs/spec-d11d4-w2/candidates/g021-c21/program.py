import itertools
import math
import random
import time

import numpy as np

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
# Ball bitmasks.
# ----------------------------------------------------------------------------

def _balls23(n, adj):
    """Return (ball2, ball3): per-vertex bitmasks of vertices within distance 2 and 3."""
    reach = [1 << v for v in range(n)]
    out2 = None
    for k in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
        if k == 1:
            out2 = reach
    return out2, reach


# ----------------------------------------------------------------------------
# Pair extension for diameter 4.
# ----------------------------------------------------------------------------

def _pair_attempt(poolX, poolY, reach2, reach3, full, d, rng, noise):
    """Greedy two-sided cover; return (SX, SY) covering everything, or None."""
    SX, SY = [], []
    uX, uY = full, full
    cx, cy = list(poolX), list(poolY)
    while uX or uY:
        capX = len(SX) < d - 1 and bool(cx)
        capY = len(SY) < d - 1 and bool(cy)
        if not capX and not capY:
            break
        cands = []
        if capX:
            for b in cx:
                g = (reach3[b] & uX).bit_count() + (reach2[b] & uY).bit_count()
                cands.append((g, 0, b))
        if capY:
            for a in cy:
                g = (reach3[a] & uY).bit_count() + (reach2[a] & uX).bit_count()
                cands.append((g, 1, a))
        best = max(c[0] for c in cands)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thr = max(1, int(best * 0.85))
            choices = [c for c in cands if c[0] >= thr]
        else:
            choices = [c for c in cands if c[0] == best]
        _, side, v = rng.choice(choices)
        if side == 0:
            SX.append(v)
            uX &= ~reach3[v]
            uY &= ~reach2[v]
            cx.remove(v)
        else:
            SY.append(v)
            uY &= ~reach3[v]
            uX &= ~reach2[v]
            cy.remove(v)
    if uX or uY:
        return None
    return SX, SY


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Single-vertex cover: S containing s0 plus up to d-1 pool vertices whose balls cover everything, or None."""
    S = [s0]
    unc = full & ~reach[s0]
    pool = [v for v in pool_all if v != s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            choices = [i for i, g in enumerate(gains) if g >= thresh]
            i = rng.choice(choices)
        else:
            top = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(top)
        bv = pool[i]
        S.append(bv)
        unc &= ~reach[bv]
        pool[i] = pool[-1]
        pool.pop()
    if unc:
        return None
    return S


def _pair_extend(n, edges, d, deadline, rng, max_fails):
    """Repeatedly insert a pair (or a single vertex as fallback) while keeping degree d and diameter 4."""
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
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if len(spare) < 2:
            break
        cols = ([v for v in spare if color[v] == 0],
                [v for v in spare if color[v] == 1])
        r2, r3 = _balls23(n, adj)
        full = (1 << n) - 1

        opts = [c for c in (0, 1) if cols[c] and cols[1 - c]]
        if opts:
            c = rng.choice(opts)
            poolX = cols[1 - c]
            poolY = cols[c]
            res = None
            for attempt in range(4):
                noise = 0.0 if attempt == 0 else rng.choice([0.15, 0.3, 0.5])
                res = _pair_attempt(poolX, poolY, r2, r3, full, d, rng, noise)
                if res is not None:
                    break
            if res is not None:
                SX, SY = res
                x, y = n, n + 1
                n += 2
                adj.append([])
                adj.append([])
                for s in SX:
                    edges.append((s, x))
                    adj[s].append(x)
                for s in SY:
                    edges.append((s, y))
                    adj[s].append(y)
                edges.append((x, y))
                adj[x] = list(SX) + [y]
                adj[y] = list(SY) + [x]
                color.append(c)
                color.append(1 - c)
                fails = 0
                continue

        # Single-vertex fallback.
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_all, r3, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
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
    return n, edges


# ----------------------------------------------------------------------------
# NEW (bold): bi-Cayley lifts over small non-abelian groups for D = 4.
#
# Group G of order N = m*k, the semidirect product Z_m x| Z_k.
# Bi-Cayley graph: A_x ~ B_{x s} for s in S, |S| = d. Left multiplication
# acts transitively on each side, so diameter <= 4 is decided from A_e alone:
#   - every B-vertex must be reached by an odd walk word s t^-1 u  (or s),
#   - every A-vertex must be reached by an even word s t^-1 or s t^-1 u v^-1.
# A simulated-annealing search over S minimises the number of uncovered
# words. Success gives a (d)-regular bipartite graph on 2N vertices, which is
# then checked exactly with lib.is_valid.
# ----------------------------------------------------------------------------

def _semidirect(m, k, r):
    """Vectorised (mul, inv) for Z_m x| Z_k with element (a, b) coded as a*k + b, and order m*k."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)

    def mul(x, y):
        a, b = x // k, x % k
        c, e = y // k, y % k
        return ((a + pw[b] * c) % m) * k + (b + e) % k

    def inv(x):
        a, b = x // k, x % k
        nb = (-b) % k
        return ((-pw[nb] * a) % m) * k + nb

    return m * k, mul, inv


def _groups(N):
    """All (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _obj(S, N, mul, inv):
    """Number of group elements not covered by the odd-walk set or the even-walk set (0 = diameter 4)."""
    Sa = np.array(S, dtype=np.int64)
    Si = inv(Sa)
    P = mul(Sa[:, None], Si[None, :])                # s t^-1
    X = mul(P[:, :, None], Sa[None, None, :])        # s t^-1 u
    E = mul(P[:, :, None, None], P[None, None, :, :])  # s t^-1 u v^-1
    odd = np.bincount(X.ravel(), minlength=N)
    ev = np.bincount(np.concatenate([P.ravel(), E.ravel(), np.array([0], dtype=np.int64)]),
                     minlength=N)
    return int(np.count_nonzero(odd == 0)) + int(np.count_nonzero(ev == 0))


def _sa(N, d, mul, inv, rng, tlim):
    """Annealing over d-subsets of Z-group elements; return a covering S or None within tlim seconds."""
    end = time.monotonic() + tlim
    S = rng.sample(range(N), d)
    f = _obj(S, N, mul, inv)
    T = 0.5
    while f > 0:
        if time.monotonic() > end:
            return None
        for _ in range(40):
            i = rng.randrange(d)
            v = rng.randrange(N)
            if v in S:
                continue
            S2 = S[:]
            S2[i] = v
            f2 = _obj(S2, N, mul, inv)
            if f2 <= f or rng.random() < math.exp(-(f2 - f) / T):
                S, f = S2, f2
                if f == 0:
                    break
        T = max(0.2, T * 0.995)
    return S


def _lift_edges(N, S, mul):
    """Bi-Cayley edges A_x ~ B_{x s}: vertices A = 0..N-1, B = N..2N-1."""
    xs = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        ys = mul(xs, int(s))
        edges.extend((int(x), N + int(y)) for x, y in zip(xs.tolist(), ys.tolist()))
    return 2 * N, edges


def _group_search(d, D, rng, end):
    """Search group bi-Cayley lifts of order N in [888, 1111] (descending); return (n, edges) or None."""
    for N in range(1111, 887, -1):
        if time.monotonic() > end:
            break
        groups = _groups(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:4]:
            left = end - time.monotonic()
            if left <= 0:
                return None
            Nn, mul, inv = _semidirect(m, k, r)
            S = _sa(Nn, d, mul, inv, rng, min(0.12, left))
            if S is not None:
                n, edges = _lift_edges(Nn, S, mul)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
    return None


# ----------------------------------------------------------------------------
# Parent pipeline (unchanged construction), run from a given incumbent.
# ----------------------------------------------------------------------------

def _parent_pipeline(d, D, rng, deadline, best):
    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            return True
        return False

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

    # Twin graph on W(d-2) followed by repeated pair extensions.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            ext_best = base
            stagnant = 0
            while time.monotonic() < deadline - 0.5 and stagnant < 6:
                now = time.monotonic()
                remaining = deadline - now
                run_end = min(deadline, now + max(2.0, remaining / 3.0))
                if rng.random() < 0.5:
                    start = ext_best
                else:
                    start = base
                try:
                    n3, e3 = _pair_extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    consider(n3, e3)
                    stagnant = 0
                else:
                    stagnant += 1
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

    # Bold branch for the target case: group bi-Cayley lifts get the first
    # slice of the budget. Accepted only if valid and larger than the incumbent.
    if d == 11 and D == 4:
        try:
            cand = _group_search(d, D, rng, t0 + 0.4 * budget)
            if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except Exception:
            pass

    try:
        best = _parent_pipeline(d, D, rng, deadline, best)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
