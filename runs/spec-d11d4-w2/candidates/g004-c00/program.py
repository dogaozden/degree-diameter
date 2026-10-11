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
# Greedy set-cover vertex extension for diameter 4 (unchanged from parent).
# ----------------------------------------------------------------------------

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


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Try to cover all vertices with R3 balls of s0 plus up to d-1 pool vertices; return the set S or None."""
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

    fails = 0
    while time.monotonic() < deadline and fails < 4000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 4000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool_all = [v for v in spare if color[v] == color[s0]]
            S = None
            for attempt in range(4):
                noise = 0.0 if attempt == 0 else 0.35
                S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
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
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# NEW: Haar-type Cayley lifts over groups Z_m x|_r Z_k, searched by hill climbing.
#
# Graph H(G, S): a_x ~ b_{x*s} for s in S, |S| = d, order 2N with N = |G|.
# Left translations are automorphisms, so diameter <= 4 is equivalent to:
#   D2*D2 = G, D2*S = G   (distances from a_0), where D2 = S*S^{-1},
#   E2*E2 = G, E2*S^{-1} = G (distances from b_0), where E2 = S^{-1}*S.
# Groups are coded as a*k+b with (a,b)(c,e) = (a + r^b c, b+e); identity is code 0.
# Search runs in parallel with the parent pipeline and keeps any valid lift.
# ----------------------------------------------------------------------------

def _gmul(X, Y, m, k, pw):
    a = X // k
    b = X % k
    c = Y // k
    e = Y % k
    return ((a + pw[b] * c) % m) * k + (b + e) % k


def _ginv(X, m, k, pw):
    a = X // k
    b = X % k
    nb = (-b) % k
    return ((-pw[nb] * a) % m) * k + nb


def _mark(z, N):
    mk = np.zeros(N, dtype=bool)
    mk[np.asarray(z).ravel()] = True
    return mk


def _haar_cost(S, N, G):
    """Number of uncovered group elements over the four diameter conditions (0 means valid)."""
    m, k, pw = G
    Si = _ginv(S, m, k, pw)
    D2 = np.flatnonzero(_mark(_gmul(S[:, None], Si[None, :], m, k, pw), N))
    E2 = np.flatnonzero(_mark(_gmul(Si[:, None], S[None, :], m, k, pw), N))
    c = 0
    c += N - int(_mark(_gmul(D2[:, None], D2[None, :], m, k, pw), N).sum())
    c += N - int(_mark(_gmul(D2[:, None], S[None, :], m, k, pw), N).sum())
    c += N - int(_mark(_gmul(E2[:, None], E2[None, :], m, k, pw), N).sum())
    c += N - int(_mark(_gmul(E2[:, None], Si[None, :], m, k, pw), N).sum())
    return int(c)


def _pick_group(N, rng):
    """Random group of order N as (m, k, pw) with k <= 12, or None if no valid r exists for the chosen k."""
    ks = [k for k in range(1, 13) if N % k == 0]
    k = rng.choice(ks)
    m = N // k
    if k == 1 or m == 1:
        return (N, 1, np.array([1], dtype=np.int64)) if m == N else (m, k, np.zeros(k, dtype=np.int64))
    rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not rs:
        return None
    r = rng.choice(rs)
    pw = [1 % m]
    for _ in range(1, k):
        pw.append(pw[-1] * r % m)
    return (m, k, np.array(pw, dtype=np.int64))


def _haar_hill(d, N, G, rng, iters, t_end):
    """Hill climb a generating set S (identity included) with |S| = d; return list S or None."""
    if N < d:
        return None
    Sl = [0] + rng.sample(range(1, N), d - 1)
    c = _haar_cost(np.array(Sl, dtype=np.int64), N, G)
    for it in range(iters):
        if c == 0:
            break
        if (it & 63) == 0 and time.monotonic() > t_end:
            break
        i = rng.randrange(1, d)
        v = rng.randrange(1, N)
        if v in Sl:
            continue
        T = list(Sl)
        T[i] = v
        ct = _haar_cost(np.array(T, dtype=np.int64), N, G)
        if ct <= c:
            Sl, c = T, ct
    return Sl if c == 0 else None


def _haar_graph(N, G, S):
    m, k, pw = G
    X = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        Y = _gmul(X, np.int64(s), m, k, pw)
        edges.extend(zip(X.tolist(), (N + Y).tolist()))
    return 2 * N, edges


def _haar_search(d, D, lo, hi, t_end, rng, best):
    """Search lifts with per-side order in [lo, hi]; ratchet upward on success. Returns best (n, edges) or best."""
    while time.monotonic() < t_end and lo <= hi:
        N = rng.randint(lo, hi)
        G = _pick_group(N, rng)
        if G is None:
            continue
        S = _haar_hill(d, N, G, rng, 2000, t_end)
        if S is None:
            continue
        n, edges = _haar_graph(N, G, S)
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            lo = N + 1
    return best


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

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    def haar_lo():
        return max(d, best[0] // 2 + 1)

    haar_ok = D == 4 and d >= 3
    hi_side = sum((d - 1) ** i for i in range(D))  # per-side Moore bound

    # Phase A: group-lift search (new construction).
    if haar_ok:
        try:
            res = _haar_search(d, D, haar_lo(), hi_side, t0 + 0.3 * budget, rng, None)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Phase B: parent pipeline.
    pstart = time.monotonic()
    pend = t0 + 0.85 * budget
    if pend > pstart:
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

        # Twin graph on W(d-2), then greedy set-cover extension using the spare slots.
        if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
            try:
                twin_deadline = pstart + 0.5 * (pend - pstart)
                n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
                consider(n2, e2)
                n3, e3 = _extend(n2, e2, d, pend, rng)
                consider(n3, e3)
            except Exception:
                pass

    # Phase C: remaining time goes back to the group-lift search.
    if haar_ok:
        try:
            res = _haar_search(d, D, haar_lo(), hi_side, deadline, rng, None)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
