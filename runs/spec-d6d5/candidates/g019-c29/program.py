import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graph (diameter 3), plus the
# K_{d,d}-type Haar graph as the always-valid fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: bipartite Cayley graphs of small semidirect products.
#
# Group G = Z_m x| Z_k with element (a, b) coded as a*k + b and
# (a, b)(c, d) = (a + r^b c, b + d), where r^k = 1 mod m and gcd(r, m) = 1.
# Take a generating set S of size d, closed under inverses, with a
# homomorphism phi: G -> Z_2 that is 1 on every element of S. Then the
# Cayley graph (g ~ g*s) is bipartite, d-regular, on |G| vertices, and
# vertex-transitive, so its diameter equals the eccentricity of the identity.
# That makes each check a single BFS.
#
# Two homomorphisms are used:
#   mode 'b': phi(a, b) = b mod 2, needs k even.
#   mode 'a': phi(a, b) = a mod 2, needs m even (r is odd, so this is a hom).
#
# Search: choose a group, then hill-climb over S by replacing one involution
# or one inverse pair at a time, maximizing the number of vertices reached
# within distance D from the identity.
# ----------------------------------------------------------------------------

def _sample_r(m, k, rng):
    """Return r with r^k = 1 mod m and gcd(r, m) = 1, or None."""
    if k == 1 or m <= 2:
        return 1
    if rng.random() < 0.2:
        return 1
    for _ in range(80):
        r = rng.randrange(2, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return r
    if pow(m - 1, k, m) == 1 % m:
        return m - 1
    return None


def _make_ops(m, k, r):
    """Return (mul, inv) for Z_m x| Z_k, elements coded as a*k + b."""
    P = [pow(r, b, m) for b in range(k)]
    NI = [(-b) % k for b in range(k)]

    def mul(x, y):
        a, b = divmod(x, k)
        c, dd = divmod(y, k)
        return ((a + P[b] * c) % m) * k + (b + dd) % k

    def inv(x):
        a, b = divmod(x, k)
        nb = NI[b]
        return ((-P[nb] * a) % m) * k + nb

    return mul, inv


def _parity(x, k, mode):
    a, b = divmod(x, k)
    return (b if mode == 'b' else a) & 1


def _score(N, mul, S, D):
    """Number of vertices reached from the identity within distance D in Cayley(G, S)."""
    seen = bytearray(N)
    seen[0] = 1
    frontier = [0]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for s in S:
                v = mul(u, s)
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        cnt += len(nxt)
        frontier = nxt
        if cnt == N or not frontier:
            break
    return cnt


def _climb(d, N, D, mul, inv, pairs, invols, rng, deadline, iters):
    """Hill-climb a generating set S of size d (inverse-closed, no identity).

    Returns S if the Cayley graph has diameter <= D, else None.
    """
    t_opts = [t for t in range(d % 2, d + 1, 2)
              if t <= len(invols) and (d - t) // 2 <= len(pairs)]
    if not t_opts:
        return None
    t = rng.choice(t_opts)
    p = (d - t) // 2

    used = set()

    def sample(kind):
        pool = invols if kind == 'i' else pairs
        if not pool:
            return None
        for _ in range(40):
            x = pool[rng.randrange(len(pool))]
            els = (x,) if kind == 'i' else (x, inv(x))
            if all(e not in used for e in els):
                return els
        return None

    units = []
    for kind, cnt in (('i', t), ('p', p)):
        for _ in range(cnt):
            els = sample(kind)
            if els is None:
                return None
            used.update(els)
            units.append((kind, els))

    def flat(us):
        return [e for _, els in us for e in els]

    S = flat(units)
    cur = _score(N, mul, S, D)
    for _ in range(iters):
        if cur == N or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(units))
        kind, old = units[idx]
        for e in old:
            used.discard(e)
        new = sample(kind)
        if new is None:
            used.update(old)
            continue
        units[idx] = (kind, new)
        S2 = flat(units)
        sc = _score(N, mul, S2, D)
        if sc >= cur:
            used.update(new)
            cur = sc
        else:
            units[idx] = (kind, old)
            used.update(old)
    if cur == N:
        return flat(units)
    return None


def _cayley_graph(N, mul, S):
    """Return (N, edges) of the Cayley graph g ~ g*s for s in S (S inverse-closed)."""
    E = set()
    for g in range(N):
        for s in S:
            h = mul(g, s)
            if g < h:
                E.add((g, h))
            elif h < g:
                E.add((h, g))
    return N, sorted(E)


def _search(d, D, moore, rng, deadline, consider, get_n):
    """Random group choice in a window just above the current best order, then climb."""
    while time.monotonic() < deadline and get_n() < moore:
        base = get_n()
        lo = base + 1
        hi = min(moore, base + max(6, base // 6))
        if lo > hi:
            break
        N = rng.randint(lo, hi)
        if N % 2:
            N += 1
        if N > hi:
            continue

        opts = []
        for k in range(1, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            if k % 2 == 0:
                opts.append((m, k, 'b'))
            if m % 2 == 0:
                opts.append((m, k, 'a'))
        if not opts:
            continue
        m, k, mode = rng.choice(opts)
        r = _sample_r(m, k, rng)
        if r is None:
            continue
        mul, inv = _make_ops(m, k, r)

        pairs, invols = [], []
        for x in range(1, N):
            if _parity(x, k, mode) != 1:
                continue
            y = inv(x)
            if y == x:
                invols.append(x)
            elif x < y:
                pairs.append(x)

        S = _climb(d, N, D, mul, inv, pairs, invols, rng, deadline, 150)
        if S is not None:
            n, e = _cayley_graph(N, mul, S)
            consider(n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Always-valid fallback: K_{d,d} as a Haar graph (diameter 2).
    fb_n, fb_e = lib.haar_graph(d, range(d))
    st = {"n": fb_n, "e": fb_e}
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"], st["e"] = n, e

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if st["n"] < moore:
            _search(d, D, moore, random.Random(seed), deadline, consider,
                    lambda: st["n"])
    except Exception:
        pass

    n, e = st["n"], st["e"]
    if lib.is_valid(n, e, d, D):
        return n, e
    return fb_n, fb_e
