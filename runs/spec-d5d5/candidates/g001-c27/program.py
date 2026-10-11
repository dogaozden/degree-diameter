import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley double covers over small groups, searched by local search.
#
# For a group G and a connection set S = {s_1..s_d} (distinct), the bipartite
# graph on G x {0,1} with edges (g,0)-(g*s,1) is d-regular on 2|G| vertices.
# Left translations are automorphisms, so distances from (e,0) and (e,1)
# determine the diameter. The search uses two BFS passes per evaluation.
#
# Groups: non-abelian matrix groups PSL/SL/PGL(2,p) (orders 60..660) and
# random semidirect products Z_m x| Z_k (any order), each as a full table.
# ----------------------------------------------------------------------------

_MATRIX_KINDS = [("PSL", 5), ("SL", 5), ("PGL", 5), ("PSL", 7),
                 ("SL", 7), ("PGL", 7), ("PSL", 11)]
_MATRIX_ORDER = {("PSL", 5): 60, ("SL", 5): 120, ("PGL", 5): 120,
                 ("PSL", 7): 168, ("SL", 7): 336, ("PGL", 7): 336,
                 ("PSL", 11): 660}
_group_cache = {}


def _matrix_group(kind, p):
    """Return (order, table, identity_index) for PSL, SL or PGL of 2x2 matrices over Z_p."""
    key = (kind, p)
    if key in _group_cache:
        return _group_cache[key]

    def canon(M):
        if kind == "PSL":
            return min(M, tuple((-x) % p for x in M))
        if kind == "PGL":
            return min(tuple((lam * x) % p for x in M) for lam in range(1, p))
        return M

    elems = set()
    for M in itertools.product(range(p), repeat=4):
        a, b, c, dd = M
        det = (a * dd - b * c) % p
        if kind == "PGL":
            if det == 0:
                continue
        elif det != 1:
            continue
        elems.add(canon(M))
    lst = sorted(elems)
    idx = {M: i for i, M in enumerate(lst)}

    def mul(X, Y):
        a, b, c, dd = X
        e, f, g, h = Y
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + dd * g) % p, (c * f + dd * h) % p)

    tab = [[idx[canon(mul(X, Y))] for Y in lst] for X in lst]
    e = idx[canon((1, 0, 0, 1))]
    res = (len(lst), tab, e)
    _group_cache[key] = res
    return res


def _semidirect(G, rng):
    """Return (order, table, identity_index=0) for a random Z_m x| Z_k of order G."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    k = rng.choice(divs)
    m = G // k
    valid = [x for x in range(1, m)
             if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
    r = rng.choice(valid) if valid else 1
    order, mul, _ = lib.semidirect_group(m, k, r)
    tab = [[mul(x, y) for y in range(order)] for x in range(order)]
    return order, tab, 0


def _cost(cols_R, cols_Ri, G, D, e):
    """Total number of (source, vertex) pairs unreached within D, for sources (e,0) and (e,1)."""
    total = 0
    for side0 in (0, 1):
        seen = [bytearray(G), bytearray(G)]
        seen[side0][e] = 1
        frontier = [e]
        side = side0
        count = 1
        for _ in range(D):
            perms = cols_R if side == 0 else cols_Ri
            other = 1 - side
            so = seen[other]
            nxt = []
            for g in frontier:
                for p in perms:
                    h = p[g]
                    if not so[h]:
                        so[h] = 1
                        nxt.append(h)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
            side = other
        total += 2 * G - count
    return total


def _search(G, tab, e, d, D, rng, t_end):
    """Hill-climb a d-element connection set S in G with zero diameter cost; None on timeout."""
    if G < d:
        return None
    inv = [row.index(e) for row in tab]
    cache = {}

    def col(s):
        c = cache.get(s)
        if c is None:
            R = [tab[g][s] for g in range(G)]
            Ri = [tab[g][inv[s]] for g in range(G)]
            c = (R, Ri)
            cache[s] = c
        return c

    def cost_of(S):
        Rs, Ris = [], []
        for s in S:
            R, Ri = col(s)
            Rs.append(R)
            Ris.append(Ri)
        return _cost(Rs, Ris, G, D, e)

    S = rng.sample(range(G), d)
    c = cost_of(S)
    stall = 0
    while c > 0:
        if time.monotonic() >= t_end:
            return None
        if stall > 1500:
            S = rng.sample(range(G), d)
            c = cost_of(S)
            stall = 0
            continue
        i = rng.randrange(d)
        s = rng.randrange(G)
        if s in S:
            continue
        T = S[:]
        T[i] = s
        c2 = cost_of(T)
        if c2 < c:
            stall = 0
        else:
            stall += 1
        if c2 <= c or rng.random() < 0.01:
            S, c = T, c2
    return S


def _graph(G, tab, S):
    """Bipartite double cover: (g,0) is vertex g, (h,1) is vertex G+h; edges (g,0)-(g*s,1)."""
    E = []
    for s in S:
        for g in range(G):
            E.append((g, G + tab[g][s]))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        try:
            if lib.is_prime_power(d - 1):
                consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        try:
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    rng = random.Random(seed * 2654435761 + d * 1009 + D)
    gmax = min(800, lib._moore_bound(d, D) // 2)
    fails = 0

    while time.monotonic() < deadline:
        best_G = best_n // 2
        if best_G >= gmax:
            break
        mats = [k for k in _MATRIX_KINDS if best_G < _MATRIX_ORDER[k] <= gmax]
        G_target = best_G + 1 + fails // 3
        try:
            use_mat = bool(mats) and (G_target > gmax or rng.random() < 0.5)
            if use_mat:
                G, tab, e = _matrix_group(*rng.choice(mats))
            elif G_target <= gmax:
                G, tab, e = _semidirect(G_target, rng)
            else:
                break
            t_end = min(deadline, time.monotonic() + 5.0)
            S = _search(G, tab, e, d, D, rng, t_end)
            if S is None:
                fails += 1
            else:
                fails = 0
                n, E = _graph(G, tab, S)
                consider(n, E)
        except Exception:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
