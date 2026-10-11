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
# Greedy set-cover vertex extension for diameter 4.
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
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
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
# Haar graphs H(Z_m, S) with |S| = d, searched randomly (cyclic baseline).
# ----------------------------------------------------------------------------

def _haar_ok(m, S, D):
    """True if the Haar graph on Z_m with connection set S has diameter <= D."""
    A = np.zeros(m, dtype=bool)
    A[0] = True
    B = np.zeros(m, dtype=bool)
    negS = [(-s) % m for s in S]
    for step in range(D):
        Y = np.zeros(m, dtype=bool)
        if step % 2 == 0:
            for s in S:
                Y |= np.roll(A, s)
            B |= Y
        else:
            for t in negS:
                Y |= np.roll(B, t)
            A |= Y
    return bool(A.all() and B.all())


def _haar_search(d, D, m_hi, rng, deadline, trials_per):
    """Binary search for the largest m with a working random Haar graph; return (m, S)."""
    lo, hi = d, max(d, m_hi)
    best = (d, list(range(d)))
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        found = None
        for _ in range(trials_per):
            if time.monotonic() >= deadline:
                break
            S = rng.sample(range(mid), d)
            if _haar_ok(mid, S, D):
                found = S
                break
        if found is not None:
            best = (mid, found)
            lo = mid
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# NEW: bi-Cayley graphs over semidirect products Z_m x|_r Z_k.
#
# Vertices a_g and b_h (g, h in G, |G| = N). a_g ~ b_{g s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the diameter is <= D iff every
# vertex is within D of a_e and within D of b_e. Each root is checked with a
# vectorised BFS over the group multiplication table. Connection sets are
# found by hill climbing on the number of vertices left uncovered.
# ----------------------------------------------------------------------------

def _semi_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k with element (a, b) coded a*k+b (identity 0), and inverse index."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    # (a, b)(c, e) = (a + r^b c, b + e)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(M == 0, axis=1)
    return M, inv


def _semi_configs(N, rng, cap):
    """Return a shuffled list of (m, k, r) with m*k = N, m >= 2, r^k = 1 mod m, gcd(r, m) = 1."""
    cfgs = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            cfgs.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > 3:
            rest = [r for r in rs if r != 1]
            rs = [1] + rng.sample(rest, 2)
        for r in rs:
            cfgs.append((m, k, r))
    rng.shuffle(cfgs)
    return cfgs[:cap]


def _bi_uncovered(M, inv, S, N, D):
    """Total number of vertices NOT within distance D of a_e plus those not within D of b_e."""
    Sarr = np.asarray(S, dtype=np.int64)
    invS = inv[Sarr]
    total = 0
    for side in (0, 1):
        seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        seen[side][0] = True
        front = np.array([0], dtype=np.int64)
        cur = side
        for _ in range(D):
            if front.size == 0:
                break
            if cur == 0:
                nxt = M[np.ix_(front, Sarr)].ravel()
                tgt = 1
            else:
                nxt = M[np.ix_(front, invS)].ravel()
                tgt = 0
            new = np.zeros(N, dtype=bool)
            new[nxt] = True
            new &= ~seen[tgt]
            seen[tgt] |= new
            front = np.flatnonzero(new)
            cur = tgt
        total += 2 * N - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _group_search(M, inv, N, d, D, deadline, rng):
    """Hill-climb a connection set S of size d in the group; return S with zero uncovered, or None."""
    S = rng.sample(range(N), d)
    cost = _bi_uncovered(M, inv, S, N, D)
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T = list(S)
        T[i] = x
        c = _bi_uncovered(M, inv, T, N, D)
        if c <= cost or rng.random() < 0.01:
            S = T
            cost = c
    return S


def _try_group_order(N, d, D, slice_end, rng):
    """Try several group structures of order N within slice_end; return (S, (m, k, r)) or None."""
    cfgs = _semi_configs(N, rng, 4)
    for idx, (m, k, r) in enumerate(cfgs):
        now = time.monotonic()
        if now >= slice_end:
            break
        share = (slice_end - now) / (len(cfgs) - idx)
        M, inv = _semi_table(m, k, r)
        S = _group_search(M, inv, N, d, D, now + share, rng)
        if S is not None:
            return S, (m, k, r)
    return None


def _group_phase(n_best, d, D, deadline, rng):
    """Binary search over the group order N for a bi-Cayley graph of order 2N beating n_best."""
    lo = n_best // 2 + 1
    hi = lib._moore_bound(d, D) // 2
    best = None
    while lo <= hi:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        N = (lo + hi) // 2
        slice_end = min(deadline, now + max(1.0, 0.35 * remaining))
        res = _try_group_order(N, d, D, slice_end, rng)
        if res is None:
            hi = N - 1
            continue
        S, (m, k, r) = res
        M, _ = _semi_table(m, k, r)
        Sarr = np.asarray(S, dtype=np.int64)
        edges = []
        for g in range(N):
            for h in M[g, Sarr]:
                edges.append((g, N + int(h)))
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            lo = N + 1
        else:
            hi = N - 1
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

    # Phase 1: random Haar graphs on Z_m (short slice).
    try:
        m_hi = max(d, lib._moore_bound(d, D) // 2)
        m, S = _haar_search(d, D, m_hi, rng, t0 + 0.1 * budget, 1500)
        consider(*lib.haar_graph(m, S))
    except Exception:
        pass

    # Phase 2: algebraic constructions (the proven parent pipeline).
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
            n2, e2 = _twin_graph(d - 2, t0 + 0.55 * budget, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, t0 + 0.62 * budget, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Phase 3: bi-Cayley search over semidirect products, aiming above the current best.
    if d >= 3 and D >= 2:
        try:
            g = _group_phase(best[0], d, D, deadline - 0.5, rng)
            if g is not None:
                consider(*g)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
