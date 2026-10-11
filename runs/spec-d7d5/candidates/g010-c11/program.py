import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Bi-Cayley lifts. Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex has degree d.
#
# Two group families now feed the same annealer:
#   * "aff": affine groups F_p^n x| H, with H a random 1-3 generator subgroup
#     of GL(n, p). These are non-solvable-looking, non-metacyclic groups that
#     the semidirect family never reaches.
#   * "semi": the parent's Z_m x| Z_k2 groups, kept as a fallback arm.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_AFF_PROB = 0.75
_AFF_FIELDS = ((2, 2), (2, 3), (3, 2), (2, 4), (5, 2), (3, 3), (7, 2), (2, 5), (3, 4), (5, 3))


# ---------------------------------------------------------- semidirect (parent)

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
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


# ------------------------------------------------------------- affine (new)

def _mat_code(M, p):
    """Hashable key for a small integer matrix."""
    return tuple(int(x) for x in M.ravel())


def _is_invertible(M, p):
    """True if the integer matrix M is invertible over GF(p) for prime p."""
    det = int(round(float(np.linalg.det(M.astype(float)))))
    return det % p != 0


def _closure(gens, p, cap):
    """Generated matrix group over GF(p), identity first; None if its order exceeds cap."""
    n = gens[0].shape[0]
    I = np.eye(n, dtype=np.int64)
    elems = [I]
    seen = {_mat_code(I, p)}
    frontier = [I]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = (x @ g) % p
                c = _mat_code(y, p)
                if c not in seen:
                    if len(elems) >= cap:
                        return None
                    seen.add(c)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems


def _sample_affine(lo, hi, rng):
    """Find (p, n, H) with F_p^n x| H of order in [lo, hi] and H a random subgroup of GL(n, p)."""
    opts = [(p, n) for p, n in _AFF_FIELDS if p ** n <= hi]
    if not opts:
        return None
    for _ in range(300):
        p, n = rng.choice(opts)
        P = p ** n
        hlo = -(-lo // P)
        hhi = hi // P
        if hhi < 1 or hlo > hhi:
            continue
        ngen = rng.choice([1, 2, 2, 3])
        gens = []
        tries = 0
        while len(gens) < ngen and tries < 200:
            tries += 1
            M = np.array([[rng.randrange(p) for _ in range(n)] for _ in range(n)], dtype=np.int64)
            if _is_invertible(M, p):
                gens.append(M)
        if not gens:
            continue
        H = _closure(gens, p, hhi)
        if H is None or len(H) < hlo:
            continue
        return p, n, H
    return None


def _affine_tables(p, n, H):
    """Return (G, Ts, Invs) for F_p^n x| H with element (v, a) coded as a*P + v.

    Product: (v, a)(w, b) = (v + a w, a b). H[0] must be the identity.
    """
    P = p ** n
    h = len(H)
    G = P * h
    pw = np.array([p ** i for i in range(n)], dtype=np.int64)
    vec = np.array([[(v // p ** i) % p for i in range(n)] for v in range(P)], dtype=np.int64)

    def enc(X):
        return (X % p) @ pw

    vadd = enc(vec[:, None, :] + vec[None, :, :])          # P x P
    Hs = np.array(H, dtype=np.int64)                        # h x n x n
    act = enc(np.einsum('aij,wj->awi', Hs, vec) % p)        # h x P : H[a] . vec[w]
    code = {_mat_code(M, p): i for i, M in enumerate(H)}
    HT = np.empty((h, h), dtype=np.int64)                   # H[a] H[b] index
    for a in range(h):
        prods = np.einsum('ij,bjk->bik', Hs[a], Hs) % p
        for b in range(h):
            HT[a, b] = code[_mat_code(prods[b], p)]

    g = np.arange(G, dtype=np.int64)
    ag = g // P
    vg = g % P
    A = act[ag[:, None], vg[None, :]]          # H[a_g] . v_s
    VA = vadd[vg[:, None], A]                  # v_g + H[a_g] v_s
    HTm = HT[ag[:, None], ag[None, :]]         # a_g a_s
    M = HTm * P + VA                           # M[g, s] = g * s
    Ts = np.ascontiguousarray(M.T)             # Ts[s, g] = g * s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(g[None, :], (G, G))
    return G, Ts, Invs


def _draw_tables(k, best_n, rng):
    """Draw a group whose 2*k*G can beat best_n. Returns (G, Ts, Invs) or None."""
    lo = best_n // (2 * k) + 1
    hi = int(lo * 1.2) + 8
    if rng.random() < _AFF_PROB:
        g = _sample_affine(lo, hi, rng)
        if g is not None:
            p, n, H = g
            return _affine_tables(p, n, H)
    target = max(2, lo + rng.randrange(0, max(2, lo // 8 + 1)))
    g = _sample_group(target, rng)
    if g is None:
        return None
    return _semidirect_tables(*g)


# ---------------------------------------------------------- annealing (parent)

def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]  # identity element is index 0
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    """Uniform start: random permutation per layer and random voltages."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs over all 2k representatives."""
    d, N = nbr.shape
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer target swaps. Returns (n, edges) or None."""
    N = 2 * k * G
    if rng.random() < _STRUCT_PROB:
        layers, S = _structured_init(d, k, G, Ts, rng)
    else:
        layers, S = _random_init(d, k, G, rng)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        try:
            tables = _draw_tables(k, best_n, rng)
        except Exception:
            tables = None
        if tables is None:
            continue
        G, Ts, Invs = tables
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        try:
            res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        except Exception:
            res = None
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
