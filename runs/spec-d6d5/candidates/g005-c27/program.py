import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Moore-type ceiling for bipartite graphs with max degree d and diameter D."""
    if D <= 0 or d <= 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley double covers of Cayley graphs over non-abelian groups.
#
# For a group G and a set S of d elements, the graph has vertices A_g = (g, 0) and
# B_h = (h, 1), with A_g adjacent to B_{g s} for every s in S. Left multiplication
# is an automorphism, so the diameter is decided by two BFS runs, from A_e and
# from B_e. Every such graph is d-regular and bipartite.
#
# WLOG e is in S: replacing S by S s0^{-1} gives an isomorphic graph.
# ----------------------------------------------------------------------------

def _table(elems, op, e_elem):
    """Multiplication table over indices: tab[a][b] = index of a*b; returns (G, tab, identity index)."""
    idx = {x: i for i, x in enumerate(elems)}
    tab = [[idx[op(a, b)] for b in elems] for a in elems]
    return len(elems), tab, idx[e_elem]


def _inverses(G, tab, e):
    inv = [0] * G
    for g in range(G):
        row = tab[g]
        for h in range(G):
            if row[h] == e:
                inv[g] = h
                break
    return inv


def _perm_even(p):
    odd = 0
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                odd ^= 1
    return odd == 0


def _b_sym(k, even):
    def f():
        elems = [p for p in itertools.permutations(range(k)) if (not even) or _perm_even(p)]
        op = lambda a, b: tuple(a[x] for x in b)
        return _table(elems, op, tuple(range(k)))
    return f


def _b_heis(p):
    """Heisenberg group of upper unitriangular 3x3 matrices over Z_p, order p^3."""
    def f():
        elems = [(a, b, c) for a in range(p) for b in range(p) for c in range(p)]
        op = lambda x, y: ((x[0] + y[0]) % p, (x[1] + y[1]) % p, (x[2] + y[2] + x[0] * y[1]) % p)
        return _table(elems, op, (0, 0, 0))
    return f


def _mat_prime(p):
    def op(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)
    return op


def _norm(x, p):
    c = next(v for v in x if v)
    if c == 1:
        return x
    ci = pow(c, p - 2, p)
    return tuple((v * ci) % p for v in x)


def _b_sl(p):
    def f():
        mp = _mat_prime(p)
        elems = [x for x in itertools.product(range(p), repeat=4)
                 if (x[0] * x[3] - x[1] * x[2]) % p == 1]
        return _table(elems, mp, (1, 0, 0, 1))
    return f


def _b_pgl(p):
    def f():
        mp = _mat_prime(p)
        elems = [x for x in itertools.product(range(p), repeat=4)
                 if (x[0] * x[3] - x[1] * x[2]) % p and _norm(x, p) == x]
        return _table(elems, lambda x, y: _norm(mp(x, y), p), (1, 0, 0, 1))
    return f


def _b_psl(p):
    mp = _mat_prime(p)

    def canon(x):
        nx = tuple((-v) % p for v in x)
        return min(x, nx)

    def f():
        elems = sorted({canon(x) for x in itertools.product(range(p), repeat=4)
                        if (x[0] * x[3] - x[1] * x[2]) % p == 1})
        return _table(elems, lambda x, y: canon(mp(x, y)), canon((1, 0, 0, 1)))
    return f


def _b_sl2_8():
    """SL(2, 8), order 504, built over GF(8)."""
    def f():
        F = lib.GF(8)
        MT = F.mul_table.tolist()
        AT = F.add_table.tolist()

        def op(x, y):
            a, b, c, d = x
            e, f_, g, h = y
            return (AT[MT[a][e]][MT[b][g]], AT[MT[a][f_]][MT[b][h]],
                    AT[MT[c][e]][MT[d][g]], AT[MT[c][f_]][MT[d][h]])

        # Characteristic 2: det = ad + bc.
        elems = [x for x in itertools.product(range(8), repeat=4)
                 if AT[MT[x[0]][x[3]]][MT[x[1]][x[2]]] == 1]
        return _table(elems, op, (1, 0, 0, 1))
    return f


def _candidates(d, D):
    """Groups whose bi-Cayley double could fit under the Moore ceiling, largest order first."""
    moore = _moore(d, D)
    spec = [
        (1.0, 660, _b_psl(11)),
        (3.0, 504, _b_sl2_8()),
        (3.0, 360, _b_sym(6, True)),
        (2.0, 343, _b_heis(7)),
        (1.0, 336, _b_pgl(7)),
        (0.5, 125, _b_heis(5)),
        (0.5, 120, _b_sym(5, False)),
        (0.5, 120, _b_sl(5)),
    ]
    out = [s for s in spec if 2 * s[1] <= moore]
    out.sort(key=lambda s: -s[1])
    return out


def _cost(tab, inv, S, G, D):
    """Ordered-by-source count of vertices not within distance D of A_e or B_e (0 iff valid)."""
    Sinv = [inv[s] for s in S]
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = tab[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = tab[u - G]
                    for si in Sinv:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _search(tab, inv, G, e, d, D, rng, deadline):
    """Hill-climb a d-subset S containing e with cost 0, restarting on stall."""
    if d < 2:
        return None
    others = [x for x in range(G) if x != e]
    if d - 1 > len(others):
        return None
    while time.monotonic() < deadline:
        S = [e] + rng.sample(others, d - 1)
        c = _cost(tab, inv, S, G, D)
        stall = 0
        while c and stall < 300:
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            x = rng.randrange(G)
            if x in S:
                stall += 1
                continue
            T = S[:]
            T[i] = x
            ct = _cost(tab, inv, T, G, D)
            if ct < c:
                stall = 0
            else:
                stall += 1
            if ct <= c or rng.random() < 0.02:
                S, c = T, ct
        if c == 0:
            return S
    return None


def _bicayley(tab, G, S):
    E = [(g, G + tab[g][s]) for g in range(G) for s in S]
    return 2 * G, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(float(time_limit), 60.0) * 0.8 - 0.5)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # PG(2, d-1) meets the Moore bound for D = 3: nothing better exists.
            if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
                return best

        cands = _candidates(d, D)
        for idx, (w, _order, bld) in enumerate(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            rest_w = sum(c[0] for c in cands[idx:])
            slice_end = min(deadline, now + (deadline - now) * w / rest_w)
            try:
                G, tab, e = bld()
            except Exception:
                continue
            if G < d or time.monotonic() >= slice_end:
                continue
            inv = _inverses(G, tab, e)
            S = _search(tab, inv, G, e, d, D, rng, slice_end)
            if S is not None:
                n, E = _bicayley(tab, G, S)
                consider(n, E)
                break  # later groups are smaller, so this is the best reachable

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
