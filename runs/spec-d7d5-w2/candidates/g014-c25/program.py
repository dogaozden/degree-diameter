import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (as in the parent).
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_PENALTY = 1000


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and layer swaps. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# NEW: double-edge-swap repair on d-regular bipartite graphs with a bitset
# reach oracle, and an incremental "grow by 2, then repair" loop.
#
# A regular bipartite graph is stored as nbr (n x d int array) plus col (0/1).
# A double-edge swap (a,b),(a2,b2) -> (a,b2),(a2,b) keeps degrees, bipartiteness
# and simplicity. _repair anneals swaps to drive the number of unordered-ordered
# pairs at distance > D to zero, biasing the moves toward defective A-vertices.
# _grow adds two vertices by splitting d-1 disjoint edges (keeps d-regularity).
# ----------------------------------------------------------------------------

def _bit_init(n):
    W = (n + 63) // 64
    R = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    R[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    return R


def _propagate(nbr, R0, D):
    d = nbr.shape[1]
    R = R0
    for _ in range(D):
        new = R.copy()
        for c in range(d):
            new |= R[nbr[:, c]]
        if np.array_equal(new, R):
            break
        R = new
    return R


def _row_counts(R):
    bits = np.unpackbits(R.view(np.uint8), axis=1)
    return bits.sum(axis=1, dtype=np.int64)


def _swap_apply(nbr, a, i, b, a2, j, b2):
    """Precondition: (a,b) at nbr[a,i], (a2,b2) at nbr[a2,j]. Afterwards edges are (a,b2), (a2,b)."""
    nbr[a, i] = b2
    nbr[a2, j] = b
    ra = int(np.flatnonzero(nbr[b] == a)[0])
    nbr[b, ra] = a2
    rb = int(np.flatnonzero(nbr[b2] == a2)[0])
    nbr[b2, rb] = a


def _pick_swap(nbr, A, defect, d, rng):
    if defect.size and rng.random() < 0.7:
        a = int(defect[rng.randrange(defect.size)])
    else:
        a = int(A[rng.randrange(A.size)])
    i = rng.randrange(d)
    b = int(nbr[a, i])
    a2 = int(A[rng.randrange(A.size)])
    j = rng.randrange(d)
    b2 = int(nbr[a2, j])
    if a == a2 or b == b2 or (nbr[a] == b2).any() or (nbr[a2] == b).any():
        return None
    return a, i, b, a2, j, b2


def _repair(nbr, col, D, rng, deadline, max_iters):
    """Anneal double-edge swaps in place. Returns True iff the graph reaches diameter <= D."""
    n, d = nbr.shape
    A = np.flatnonzero(col == 0)
    R0 = _bit_init(n)
    cnt = _row_counts(_propagate(nbr, R0, D))
    cost = n * n - int(cnt.sum())
    if cost == 0:
        return True
    c0 = float(cost)
    it = 0
    while cost > 0 and it < max_iters and time.monotonic() < deadline:
        frac = it / max_iters
        T = max(0.5, max(2.0, c0 / (4.0 * n)) * (1.0 - frac))
        it += 1
        defect = A[cnt[A] < n]
        mv = _pick_swap(nbr, A, defect, d, rng)
        if mv is None:
            continue
        a, i, b, a2, j, b2 = mv
        _swap_apply(nbr, a, i, b, a2, j, b2)
        cnt2 = _row_counts(_propagate(nbr, R0, D))
        cost2 = n * n - int(cnt2.sum())
        if cost2 <= cost or rng.random() < math.exp(-(cost2 - cost) / T):
            cost, cnt = cost2, cnt2
        else:
            _swap_apply(nbr, a, i, b2, a2, j, b)  # undo
    return cost == 0


def _grow(nbr, col, rng):
    """Add two vertices x (side 0), y (side 1) by splitting d-1 disjoint edges. Returns (nbr, col) or None."""
    n, d = nbr.shape
    if d < 2:
        return None
    x, y = n, n + 1
    A = [int(a) for a in np.flatnonzero(col == 0)]
    rng.shuffle(A)
    used_b = set()
    chosen = []
    for a in A:
        if len(chosen) == d - 1:
            break
        idxs = [i for i in range(d) if int(nbr[a, i]) not in used_b]
        if not idxs:
            continue
        i = idxs[rng.randrange(len(idxs))]
        b = int(nbr[a, i])
        used_b.add(b)
        chosen.append((a, i, b))
    if len(chosen) < d - 1:
        return None
    big = np.vstack([nbr, np.zeros((2, d), dtype=np.int64)])
    for a, i, b in chosen:
        big[a, i] = y
        k = int(np.flatnonzero(big[b] == a)[0])
        big[b, k] = x
    big[x, :d - 1] = [b for _, _, b in chosen]
    big[x, d - 1] = y
    big[y, :d - 1] = [a for a, _, _ in chosen]
    big[y, d - 1] = x
    col2 = np.concatenate([col, np.array([0, 1], dtype=np.int64)])
    return big, col2


def _to_edges(nbr, col):
    n = nbr.shape[0]
    edges = []
    for a in np.flatnonzero(col == 0):
        a = int(a)
        for b in nbr[a]:
            edges.append((a, int(b)))
    return n, edges


def _regular_from_edges(n, edges, d):
    """Return (nbr, col) numpy arrays if the graph is simple, bipartite and d-regular, else None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _two_color(n, edges)
    if color is None:
        return None
    return np.array(adj, dtype=np.int64), np.array(color, dtype=np.int64)


def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.4 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Best d-regular starting graph for the repair phase.
    reg = None
    reg_n = 0
    hn, he = lib.haar_graph(d, range(d))
    conv = _regular_from_edges(hn, he, d)
    if conv is not None:
        reg, reg_n = conv, hn

    # Phase 1: lift search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    try:
        while time.monotonic() < search_deadline:
            k = pick_k()
            base = max(best_n, reg_n) // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= max(best_n, reg_n):
                continue
            trials[k] += 1
            res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
                if res[0] > reg_n:
                    c = _regular_from_edges(res[0], res[1], d)
                    if c is not None:
                        reg, reg_n = c, res[0]
    except Exception:
        pass

    # Phase 2: grow by 2 and repair with double-edge swaps.
    try:
        if reg is not None:
            cur_nbr, cur_col = reg
            fails = 0
            while time.monotonic() < deadline - 1.0 and fails < 200:
                g = _grow(cur_nbr, cur_col, rng)
                if g is None:
                    fails += 1
                    continue
                nb2, col2 = g
                ok = _repair(nb2, col2, D, rng, deadline - 0.5, 500)
                if not ok:
                    fails += 1
                    continue
                fails = 0
                cur_nbr, cur_col = nb2, col2
                n2, e2 = _to_edges(nb2, col2)
                if n2 > best_n and not consider(n2, e2):
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
