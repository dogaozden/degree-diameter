import math
import random
import time

import lib

SLICE = 2.0  # seconds given to each (group order, group) annealing attempt


def _safe_base(d):
    """Return a validated structured D = 3 base graph, or None."""
    try:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            base = lib.projective_plane_incidence(d - 1)   # Moore-optimal
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)           # record-level, degree d
        else:
            return None
        if lib.is_valid(base[0], base[1], d, 3):
            return base
    except Exception:
        pass
    return None


def _group_options(m, rng):
    """Return up to three (order, mul, inv) groups of order m: cyclic, plus semidirect products."""
    opts = [lib.cyclic_group(m)]
    divs = [b for b in range(2, m) if m % b == 0 and m // b >= 3]
    rng.shuffle(divs)
    for b in divs:
        a = m // b
        rs = [r for r in range(2, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1]
        if rs:
            try:
                opts.append(lib.semidirect_group(a, b, rng.choice(rs)))
            except ValueError:
                pass
        if len(opts) >= 3:
            break
    return opts


def _tables(m, mul, inv):
    mt = [[mul(x, y) for y in range(m)] for x in range(m)]
    it = [inv(x) for x in range(m)]
    return mt, it


def _uncovered(S, mt, it, m):
    """Number of group elements not in S·S^-1 and not in S^-1·S (bi-Cayley diameter-3 conditions)."""
    c = set()
    for s in S:
        row = mt[s]
        irow = mt[it[s]]
        for t in S:
            c.add(row[it[t]])   # s t^-1
            c.add(irow[t])      # s^-1 t
    return m - len(c)


def _anneal(m, k, mt, it, rng, t_end):
    """Search for a k-subset S containing the identity (0) that covers the group."""
    while time.monotonic() < t_end:
        S = [0] + rng.sample(range(1, m), k - 1)
        cur = _uncovered(S, mt, it, m)
        T = 1.0
        for _ in range(6000):
            if cur == 0:
                return S
            i = rng.randrange(1, k)
            g = rng.randrange(1, m)
            if g in S:
                continue
            old = S[i]
            S[i] = g
            new = _uncovered(S, mt, it, m)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
            else:
                S[i] = old
            T = max(0.05, T * 0.999)
        if cur == 0:
            return S
    return None


def _search(d, lo, hi, rng, t_end):
    """Bi-Cayley lifts: vertices A = G and B = G, a_x ~ b_{x s} for s in S, |S| = d.

    Diameter 3 needs S S^-1 = G and S^-1 S = G, which forces |G| <= d^2 - d + 1.
    Tries group orders ascending from lo and keeps the largest valid success.
    """
    best = None
    k = d
    for m in range(max(lo, k + 1), hi + 1):
        for order, mul, inv in _group_options(m, rng):
            now = time.monotonic()
            if now >= t_end:
                return best
            if order != m:
                continue
            mt, it = _tables(m, mul, inv)
            S = _anneal(m, k, mt, it, rng, min(t_end, now + SLICE))
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, s) for s in S], m, mul)
            if lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                break
    return best


def _haar_fallback(d, D, rng, deadline):
    """Parent-style random Haar graphs for cases without a structured base."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.72 * time_limit
    rng = random.Random(seed)
    k_top = d * d - d + 1  # largest bi-Cayley group order allowed for D = 3

    best = None
    if D == 3 and d >= 2:
        base = _safe_base(d)
        is_pg = d - 1 >= 2 and lib.is_prime_power(d - 1)
        if base is not None and is_pg:
            return base  # projective plane incidence graph meets the Moore bound

        if base is not None:
            lo = base[0] // 2 + 1          # need strictly more than base order
        else:
            lo = int(0.85 * k_top)
        cand = _search(d, lo, k_top, rng, deadline)
        if cand is not None and (base is None or cand[0] > base[0]):
            best = cand
        elif base is not None:
            best = base

    if best is None:
        best = _haar_fallback(d, D, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    return best
