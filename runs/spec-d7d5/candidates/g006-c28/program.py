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
# Bi-Cayley lifts over a finite group G with k base vertices per side.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d.
#
# Groups come from two families:
#   * semidirect products Z_m x| Z_k2 (random sampling, as before);
#   * NEW: projective line groups PSL(2,p) and PGL(2,p) realised as permutation
#     groups on p+1 points (non-metacyclic, so structurally different from the
#     cyclic/semidirect lifts that stalled below the record).
# Search is simulated annealing over voltages and per-layer target swaps.
# Cost = number of unreached (representative, vertex) pairs.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_PERM_PROB = 0.7

# (kind, p, k): kind "psl" = PSL(2,p), "pgl" = PGL(2,p); base size k.
# Orders: PSL(2,p) = p(p^2-1)/2, PGL(2,p) = p(p^2-1). Lifts have 2*k*order vertices.
_PERM_CFGS = [
    ("psl", 5, 10), ("psl", 5, 11), ("psl", 5, 12), ("psl", 5, 13),
    ("psl", 7, 4), ("pgl", 7, 2), ("psl", 7, 5), ("pgl", 7, 3),
    ("psl", 11, 1), ("psl", 13, 1), ("pgl", 11, 1), ("psl", 11, 2),
]


def _perm_order(kind, p):
    return p * (p * p - 1) // 2 if kind == "psl" else p * (p * p - 1)


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

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, built with one numpy broadcast.
    Identity is index 0.
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


def _prim_root(p):
    """Smallest primitive root modulo the prime p."""
    for a in range(2, p):
        x, t = a, 1
        while x != 1:
            x = x * a % p
            t += 1
        if t == p - 1:
            return a
    return 1


def _proj_line_gens(p, full):
    """Permutation generators of PSL(2,p) (full=False) or PGL(2,p) (full=True) on points 0..p (p = infinity)."""
    a = _prim_root(p)
    c = a if full else a * a % p
    inf = p
    t = tuple([(x + 1) % p for x in range(p)] + [inf])
    mu = tuple([(c * x) % p for x in range(p)] + [inf])
    iv = tuple([inf] + [(-pow(x, p - 2, p)) % p for x in range(1, p)] + [0])
    return [t, mu, iv]


def _perm_closure(gens, n_pts, cap):
    """All elements of the permutation group generated by gens; identity first. None if above cap."""
    ident = tuple(range(n_pts))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        p = elems[i]
        i += 1
        for g in gens:
            q = tuple(g[x] for x in p)  # apply p, then g
            if q not in index:
                if len(elems) >= cap:
                    return None
                index[q] = len(elems)
                elems.append(q)
    return elems


def _perm_tables(elems):
    """Return (G, Ts, Invs) for a permutation group given as a list of perms (identity first)."""
    E = np.array(elems, dtype=np.int64)
    G, n = E.shape
    w = np.array([n ** j for j in range(n)], dtype=np.int64)
    codes = E @ w
    order = np.argsort(codes)
    sorted_codes = codes[order]
    Ts = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        comp = E[s][E]          # comp[g, x] = s(g(x)): g*s = apply g then s
        cc = comp @ w
        pos = np.searchsorted(sorted_codes, cc)
        Ts[s] = order[pos]
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(np.arange(G, dtype=np.int64)[None, :], (G, G))
    return G, Ts, Invs


def _perm_group(kind, p):
    """Return (G, Ts, Invs) for PSL(2,p) or PGL(2,p), or None if the closure is too large."""
    gens = _proj_line_gens(p, kind == "pgl")
    elems = _perm_closure(gens, p + 1, 1500)
    if elems is None:
        return None
    return _perm_tables(elems)


def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]
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
    """Unreached (representative, vertex) pairs over all 2k representatives (bit b = block b)."""
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
    return 2 * k * N - int(_POP[reach & 0xFFFF].sum()) - int(_POP[(reach >> 16) & 0xFFFF].sum()) \
        - int(_POP[(reach >> 32) & 0xFFFF].sum()) - int(_POP[(reach >> 48) & 0xFFFF].sum())


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


def _pick(cands, tries, wins, rng):
    """Bandit choice among candidate indices by success rate, with exploration."""
    if rng.random() < 0.2:
        return rng.choice(cands)
    return max(cands, key=lambda i: (wins[i] + 1) / (tries[i] + 2) + 0.02 * rng.random())


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    moore = lib._moore_bound(d, D)

    # Permutation-group family state.
    tables = {}
    bad = set()
    perm_tries = [0] * len(_PERM_CFGS)
    perm_wins = [0] * len(_PERM_CFGS)

    # Semidirect family state (as before).
    sd_tries = {k: 0 for k in _KS}
    sd_wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (sd_wins[k] + 1) / (sd_tries[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        if rng.random() < _PERM_PROB:
            cands = []
            for i, (kind, p, k) in enumerate(_PERM_CFGS):
                if (kind, p) in bad:
                    continue
                N = 2 * k * _perm_order(kind, p)
                if best_n < N <= moore:
                    cands.append(i)
            if cands:
                i = _pick(cands, perm_tries, perm_wins, rng)
                kind, p, k = _PERM_CFGS[i]
                key = (kind, p)
                if key not in tables:
                    tables[key] = _perm_group(kind, p)
                    if tables[key] is None:
                        bad.add(key)
                        continue
                G, Ts, Invs = tables[key]
                if 2 * k * G <= best_n or 2 * k * G > moore:
                    continue
                perm_tries[i] += 1
                res = _search(d, D, k, G, Ts, Invs, rng, deadline, 20000)
                if res is not None:
                    perm_wins[i] += 1
                    consider(res[0], res[1])
                continue

        # Semidirect fallback family.
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n or 2 * k * G > moore:
            continue
        sd_tries[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None:
            sd_wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
