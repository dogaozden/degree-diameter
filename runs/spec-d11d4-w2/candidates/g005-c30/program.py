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
# NEW: multi-fibre cyclic/semidirect voltage lifts with local search.
#
# Base graph: k A-vertices and k B-vertices. The dart multiplicity matrix M
# (k x k) has all row and column sums equal to d, so the lift is d-regular.
# Each dart (i, j) carries a group voltage h; darts in the same class (i, j)
# need distinct voltages so the lift is simple. Vertices are (A_i, x) and
# (B_j, y) with x, y in the group G; (A_i, x) ~ (B_j, x*h) for each dart.
#
# Left multiplication is an automorphism, so the lift is fibre-transitive and
# it suffices to check eccentricities of the 2k fibre identities. Every
# candidate is still re-checked with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

def _perm_matrix_sum(k, d, rng):
    """Sum of d random permutation matrices: a k x k integer matrix with all row and column sums d."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            M[i][p[i]] += 1
    return M


def _slots(M, k, d):
    """Expand matrix M into per-A-vertex slot arrays Aj (k, d). Return None if the column sums are not d."""
    for j in range(k):
        if sum(M[i][j] for i in range(k)) != d:
            return None
    Aj = np.zeros((k, d), dtype=np.int64)
    for i in range(k):
        if sum(M[i]) != d:
            return None
        t = 0
        for j in range(k):
            for _ in range(M[i][j]):
                Aj[i, t] = j
                t += 1
    return Aj


def _init_volt(k, d, Aj, G, rng):
    """Random voltages, distinct within each (i, j) dart class."""
    Ah = np.zeros((k, d), dtype=np.int64)
    for i in range(k):
        for j in set(Aj[i].tolist()):
            pos = [t for t in range(d) if Aj[i, t] == j]
            vals = rng.sample(range(G), len(pos))
            for t, v in zip(pos, vals):
                Ah[i, t] = v
    return Ah


def _nbr(k, d, G, T, invT, Aj, Ah):
    """Neighbour table (2kG, d) of the lift. Rows 0..kG-1 are A-side, rows kG.. are B-side."""
    TA = T[:, Ah].transpose(1, 0, 2)                  # (k, G, d)
    nA = (k + Aj)[:, None, :] * G + TA
    idx = np.argsort(Aj.ravel(), kind="stable").reshape(k, d)
    Bi = np.arange(k).repeat(d)[idx]                  # A index of each dart at B_j
    Bh = Ah.ravel()[idx]                              # voltage of each dart at B_j
    TB = T[:, invT[Bh]].transpose(1, 0, 2)            # (k, G, d)
    nB = Bi[:, None, :] * G + TB
    return np.concatenate([nA.reshape(k * G, d), nB.reshape(k * G, d)])


def _bad(nbr, N, srcs, D):
    """Total number of vertices not within distance D of the given source vertices."""
    total = 0
    for s in srcs:
        reached = np.zeros(N, dtype=bool)
        reached[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[fr].ravel()
            nxt = nxt[~reached[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            reached[nxt] = True
            fr = nxt
        total += N - int(np.count_nonzero(reached))
    return total


def _climb(k, d, G, T, invT, Aj, Ah, D, deadline, rng):
    """Local search over voltages. Return Ah with zero bad pairs, or None at the deadline."""
    N = 2 * k * G
    srcs = [i * G for i in range(2 * k)]

    def bad(A):
        return _bad(_nbr(k, d, G, T, invT, Aj, A), N, srcs, D)

    cur = bad(Ah)
    it = 0
    while cur > 0:
        if (it & 15) == 0 and time.monotonic() >= deadline:
            return None
        it += 1
        i = rng.randrange(k)
        s = rng.randrange(d)
        j = Aj[i, s]
        used = {int(Ah[i, t]) for t in range(d) if Aj[i, t] == j and t != s}
        while True:
            h = rng.randrange(G)
            if h not in used:
                break
        old = Ah[i, s]
        Ah[i, s] = h
        new = bad(Ah)
        if new <= cur or rng.random() < 0.02:
            cur = new
        else:
            Ah[i, s] = old
    return Ah


def _lift_edges(k, d, G, T, Aj, Ah):
    """Edges of the lift from the A-side darts: (n, edges)."""
    TA = T[:, Ah].transpose(1, 0, 2)
    nA = ((k + Aj)[:, None, :] * G + TA).reshape(k * G, d)
    src = np.repeat(np.arange(k * G), d)
    dst = nA.ravel()
    return 2 * k * G, list(zip(src.tolist(), dst.tolist()))


def _run_cyclic(k, d, D, Aj, G, deadline, rng, consider):
    """Ladder search over the group order G for a fixed base matrix, using cyclic groups Z_G."""
    step = max(1, G // 50)
    G_ok = None
    while time.monotonic() < deadline:
        if G <= d:
            break
        now = time.monotonic()
        att = min(deadline, now + 0.5 * (deadline - now))
        X = np.arange(G)
        T = (X[:, None] + X[None, :]) % G
        invT = np.argmax(T == 0, axis=1)
        Ah = _init_volt(k, d, Aj, G, rng)
        res = _climb(k, d, G, T, invT, Aj, Ah, D, att, rng)
        if res is not None:
            n, edges = _lift_edges(k, d, G, T, Aj, res)
            consider(n, edges)
            G_ok = G
            G = G + step
        else:
            if G_ok is None:
                G = G - step
                if G <= d:
                    break
            else:
                step //= 2
                if step == 0:
                    break
                G = G_ok + step


def _lift_phase(d, D, moore, deadline, rng, consider):
    """Run voltage-lift searches over several base matrices, sharing time equally."""
    if d < 3 or D < 2:
        return
    mats = [(1, [[d]])]
    for a in range(1, d // 2 + 1):
        mats.append((2, [[a, d - a], [d - a, a]]))
    for k in (3, 4):
        for _ in range(2):
            mats.append((k, _perm_matrix_sum(k, d, rng)))
    prepared = []
    for k, M in mats:
        Aj = _slots(M, k, d)
        if Aj is None:
            continue
        G0 = max(d + 1, int(0.7 * moore / (2 * k)))
        prepared.append((k, Aj, G0))
    for idx, (k, Aj, G0) in enumerate(prepared):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(prepared) - idx)
        try:
            _run_cyclic(k, d, D, Aj, G0, slice_end, rng, consider)
        except Exception:
            pass


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
    moore = lib.moore_bound(d, D)

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if best[0] >= moore:
        return best

    # Phase 1: projective plane for D = 3 when d-1 is a prime power (meets the Moore bound).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        if best[0] >= moore:
            return best

    # Phase 2: NEW voltage-lift search over multi-fibre base graphs.
    try:
        _lift_phase(d, D, moore, t0 + 0.4 * budget, rng, consider)
    except Exception:
        pass
    if best[0] >= moore:
        return best

    # Phase 3: algebraic constructions with the remaining time (parent pipeline).
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            twin_deadline = now + 0.5 * (deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
