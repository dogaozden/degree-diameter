import itertools
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


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Cover all vertices using R3(s0) plus up to d-1 pool vertices; return the chosen set S or None."""
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


def _extend(n, edges, d, deadline, rng, max_fails):
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
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
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
    return n, edges


# ----------------------------------------------------------------------------
# Bold new construction: Z_m voltage lifts of a d-regular bipartite base
# multigraph on k+k fibres. Base dart (i, u) joins A-fibre u to B-fibre
# sig[i][u] with voltage vol[i][u]; the lift has 2*k*m vertices and degree d.
# Z_m acts on every fibre, so eccentricities are constant on fibres and only
# one representative per fibre needs a distance check.
# ----------------------------------------------------------------------------

def _lift_nbr(sig, vol, k, m, d):
    """Neighbour table (2km x d). A-vertex u*m+x is joined to B-vertex sig[i,u]*m+(x+vol[i,u])%m."""
    X = np.arange(m, dtype=np.int64)
    sinv = np.argsort(sig, axis=1).astype(np.int64)   # sinv[i, v] = u with sig[i, u] = v
    sigT = sig.T.astype(np.int64)
    volT = vol.T.astype(np.int64)
    nbrA = k * m + sigT[:, None, :] * m + (X[None, :, None] + volT[:, None, :]) % m
    U = sinv.T                                         # U[v, i]
    G = vol[np.arange(d)[None, :], U].astype(np.int64)  # G[v, i] = vol[i, U[v, i]]
    nbrB = U[:, None, :] * m + (X[None, :, None] - G[:, None, :]) % m
    return np.concatenate([nbrA.reshape(k * m, d), nbrB.reshape(k * m, d)], axis=0)


def _lift_cost(nbr, k, m, D):
    """Number of (fibre representative, vertex) pairs at distance > D (0 means diameter <= D)."""
    n = nbr.shape[0]
    R = np.zeros((2 * k, n), dtype=bool)
    reps = np.concatenate([np.arange(k) * m, k * m + np.arange(k) * m])
    R[np.arange(2 * k), reps] = True
    for _ in range(D):
        R = R | R[:, nbr].any(axis=2)
    return 2 * k * n - int(R.sum())


def _lift_try(d, D, k, m, deadline, gen):
    """Local search over permutations and voltages; return a neighbour table with cost 0, or None."""
    sig = np.stack([gen.permutation(k) for _ in range(d)]).astype(np.int64)
    vol = gen.integers(0, m, size=(d, k)).astype(np.int64)
    nbr = _lift_nbr(sig, vol, k, m, d)
    cost = _lift_cost(nbr, k, m, D)
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        if k >= 2 and gen.random() < 0.3:
            i = int(gen.integers(d))
            u1, u2 = (int(x) for x in gen.choice(k, 2, replace=False))
            sig[i, u1], sig[i, u2] = sig[i, u2], sig[i, u1]
            nb2 = _lift_nbr(sig, vol, k, m, d)
            c2 = _lift_cost(nb2, k, m, D)
            if c2 <= cost or gen.random() < 0.02:
                nbr, cost = nb2, c2
            else:
                sig[i, u1], sig[i, u2] = sig[i, u2], sig[i, u1]
        else:
            i = int(gen.integers(d))
            u = int(gen.integers(k))
            old = int(vol[i, u])
            vol[i, u] = (old + int(gen.integers(1, m))) % m
            nb2 = _lift_nbr(sig, vol, k, m, d)
            c2 = _lift_cost(nb2, k, m, D)
            if c2 <= cost or gen.random() < 0.02:
                nbr, cost = nb2, c2
            else:
                vol[i, u] = old
    return nbr


def _lift_edges(nbr, km):
    """Edge list (A index < B index) of a lift from its neighbour table."""
    rows = nbr[:km].tolist()
    return sorted({(a, b) for a, row in enumerate(rows) for b in row})


def _lift_phase(d, D, deadline, rng, consider):
    """Run lift searches with decreasing or increasing target order until the deadline."""
    gen = np.random.default_rng(rng.randrange(1 << 31))
    K = 888                      # fibre-vertices per side target: n = 2K >= 1776
    ks = [10, 12, 9, 15, 8]
    attempt = 0
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 2.0:
            break
        k = ks[attempt % len(ks)]
        attempt += 1
        m = -(-K // k)
        slice_len = max(3.0, min(12.0, remaining / 3.0))
        end = min(deadline, now + slice_len)
        try:
            nbr = _lift_try(d, D, k, m, end, gen)
        except Exception:
            nbr = None
        if nbr is None:
            K = max(400, K - 4)
            continue
        n = 2 * k * m
        edges = _lift_edges(nbr, k * m)
        if consider(n, edges):
            K = max(K, n // 2 + 6)
        else:
            K = max(400, K - 4)


# ----------------------------------------------------------------------------
# Parent pipeline (twin construction plus extensions), used as a second stage.
# ----------------------------------------------------------------------------

def _parent_pipeline(d, D, rng, deadline, consider):
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

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
                    n3, e3 = _extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    consider(n3, e3)
                    stagnant = 0
                else:
                    stagnant += 1


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
    holder = {"best": lib.haar_graph(d, range(d))}

    def consider(n, edges):
        if n > holder["best"][0] and lib.is_valid(n, edges, d, D):
            holder["best"] = (n, edges)
            return True
        return False

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Stage 1 (bold): voltage lifts over Z_m with a searched d-regular base.
    if D >= 4 and d >= 4:
        now = time.monotonic()
        lift_deadline = now + 0.5 * (deadline - now)
        try:
            _lift_phase(d, D, lift_deadline, rng, consider)
        except Exception:
            pass

    # Stage 2: parent construction with the remaining time.
    try:
        _parent_pipeline(d, D, rng, deadline, consider)
    except Exception:
        pass

    best = holder["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
