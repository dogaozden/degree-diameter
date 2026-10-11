import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over explicit groups (new family for D >= 3).
#
# Group G with identity at index 0 and multiplication table M[x, y] = x*y.
# Vertices A_x = x and B_w = G + w. Edges A_x ~ B_{x*s} for s in S (|S| = d).
# Left multiplication is an automorphism, so diameter <= D holds iff every
# vertex is within distance D of A_1 and of B_1.
#
# Groups used: Heisenberg H(7) (order 343), AGL(1,19) (order 342), a random
# generating pair of A6 (order 360), and semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _semidirect(m, k, r):
    """Z_m x| Z_k with element (a, b) coded a*k + b; (a,b)(c,d) = (a + r^b c, b + d)."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A1, B1 = a[:, None], b[:, None]
    A2, B2 = a[None, :], b[None, :]
    Am = (A1 + pw[B1] * A2) % m
    Bm = (B1 + B2) % k
    return G, Am * k + Bm


def _affine(p):
    """AGL(1,p): element (u-1)*p + b encodes x -> u*x + b."""
    G = p * (p - 1)
    idx = np.arange(G, dtype=np.int64)
    u = idx // p + 1
    b = idx % p
    u1, b1 = u[:, None], b[:, None]
    u2, b2 = u[None, :], b[None, :]
    Uo = (u1 * u2) % p
    Bo = (u1 * b2 + b1) % p
    return G, (Uo - 1) * p + Bo


def _heis(p):
    """Heisenberg group over Z_p: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    G = p ** 3
    idx = np.arange(G, dtype=np.int64)
    a = idx // (p * p)
    b = (idx // p) % p
    c = idx % p
    a1, b1, c1 = a[:, None], b[:, None], c[:, None]
    a2, b2, c2 = a[None, :], b[None, :], c[None, :]
    A = (a1 + a2) % p
    B = (b1 + b2) % p
    C = (c1 + c2 + a1 * b2) % p
    return G, A * p * p + B * p + C


def _parity(p):
    s = 0
    n = len(p)
    for i in range(n):
        for j in range(i + 1, n):
            if p[i] > p[j]:
                s ^= 1
    return s


def _perm360(rng):
    """A random 2-generated subgroup of A6 of order exactly 360, as a multiplication table."""
    npts = 6
    ident = tuple(range(npts))

    def compose(g, x):
        return tuple(g[i] for i in x)

    for _ in range(200):
        gens = []
        while len(gens) < 2:
            p = list(range(npts))
            rng.shuffle(p)
            if _parity(p) == 0:
                gens.append(tuple(p))
        elems = [ident]
        index = {ident: 0}
        frontier = [ident]
        ok = True
        while frontier and ok:
            nxt = []
            for x in frontier:
                for g in gens:
                    y = compose(g, x)
                    if y not in index:
                        if len(elems) >= 360:
                            ok = False
                            break
                        index[y] = len(elems)
                        elems.append(y)
                        nxt.append(y)
                if not ok:
                    break
            frontier = nxt
        if ok and len(elems) == 360:
            M = np.array([[index[compose(a, b)] for b in elems] for a in elems],
                         dtype=np.int64)
            return 360, M
    return None


def _specs(lo, hi):
    """Group specifications with order in [lo, hi], sorted by order ascending."""
    out = []
    for p in range(3, hi + 2):
        if _is_prime(p) and lo <= p * (p - 1) <= hi:
            out.append((p * (p - 1), ("AFF", p)))
    if lo <= 343 <= hi:
        out.append((343, ("H", 7)))
    if lo <= 360 <= hi:
        out.append((360, ("PERM",)))
    for o in range(max(lo, 4), hi + 1):
        for k in range(1, o + 1):
            if o % k:
                continue
            m = o // k
            if m < 2:
                continue
            if k == 1:
                out.append((o, ("SD", m, 1, 1)))
                continue
            rs = [r for r in range(2, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1][:2]
            for r in rs:
                out.append((o, ("SD", m, k, r)))
    out.sort(key=lambda t: t[0])
    return out


def _unreached(adj, src, D):
    N = adj.shape[0]
    seen = np.zeros(N, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        nb = adj[frontier].ravel()
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        seen[nb] = True
        frontier = nb
    return N - int(np.count_nonzero(seen))


def _cost(M, inv, S, G, D):
    Sa = np.asarray(S, dtype=np.int64)
    adj = np.vstack([G + M[:, Sa], M[:, inv[Sa]]])
    return _unreached(adj, 0, D) + _unreached(adj, G, D)


def _anneal(M, inv, G, d, D, deadline, rng, iters):
    """Search S (|S| = d) with zero cost; restart from random sets until the deadline."""
    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = _cost(M, inv, S, G, D)
        T = 1.0
        for _ in range(iters):
            if c == 0 or time.monotonic() >= deadline:
                break
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            S2 = S[:]
            S2[i] = x
            c2 = _cost(M, inv, S2, G, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = S2, c2
            T = max(0.05, T * 0.995)
        if c == 0:
            return S
    return None


def _edges(M, S, G):
    E = []
    for x in range(G):
        for s in S:
            E.append((x, G + int(M[x, s])))
    return 2 * G, E


def _bicayley(d, D, lo, hi, deadline, rng, consider, cur_G):
    specs = _specs(lo, hi)
    perm_rng = random.Random(4242)
    perm_cache = {}

    def build(spec):
        kind = spec[0]
        if kind == "AFF":
            G, M = _affine(spec[1])
        elif kind == "H":
            G, M = _heis(spec[1])
        elif kind == "SD":
            G, M = _semidirect(spec[1], spec[2], spec[3])
        else:
            if "p" not in perm_cache:
                perm_cache["p"] = _perm360(perm_rng)
            res = perm_cache["p"]
            if res is None:
                return None
            G, M = res
        ar = np.arange(G)
        if not (np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar)):
            return None
        inv = np.argmax(M == 0, axis=1)
        return G, M, inv

    def attempt(spec, budget_s):
        try:
            grp = build(spec)
        except Exception:
            return False
        if grp is None:
            return False
        G, M, inv = grp
        sub = min(deadline, time.monotonic() + budget_s)
        S = _anneal(M, inv, G, d, D, sub, rng, 1200)
        if S is None:
            return False
        n, e = _edges(M, S, G)
        return consider(n, e)

    # Special groups first, each with a generous budget.
    for o, spec in specs:
        if spec in (("AFF", 19), ("H", 7), ("PERM",)):
            if time.monotonic() >= deadline:
                return
            if o > cur_G():
                attempt(spec, 4.0)

    # Ladder: ascending order, rounds with growing per-group budgets.
    budget_s = 0.5
    while time.monotonic() < deadline:
        pending = [(o, s) for o, s in specs if o > cur_G()]
        if not pending:
            return
        for o, spec in pending:
            if time.monotonic() >= deadline:
                return
            if o <= cur_G():
                continue
            attempt(spec, budget_s)
        budget_s *= 1.8


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed * 1000003 + d * 97 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, list(range(d)))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    def cur_G():
        return best[0] // 2

    # Exact projective-plane incidence graph for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n3, e3 = lib.projective_plane_incidence(d - 1)
        consider(n3, e3)

    # New family: bi-Cayley graphs over explicit non-abelian groups.
    if D >= 3 and d >= 3 and best[0] < moore and time.monotonic() < deadline:
        lo = max(2 * d, int(0.19 * moore))
        hi = int(0.275 * moore)
        _bicayley(d, D, lo, hi, deadline, rng, consider, cur_G)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, list(range(d)))
    return best
