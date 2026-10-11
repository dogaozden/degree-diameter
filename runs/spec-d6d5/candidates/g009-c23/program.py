import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Classical baselines (kept as safe fallbacks; valid for the stated diameters).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# New bold family: single-orbit bi-Cayley graphs over semidirect products
# Z_m x| Z_k (orders G = m*k, graph order 2G, degree d).
#
# Vertices: A_g = g and B_h = G + h, for g, h in the group.
# Connection set S = {s_1..s_d} (distinct): A_g ~ B_{g*s}.
#
# Left multiplication is an automorphism, transitive on each side, so the
# diameter is exactly checked by BFS from A_e and from B_e. This makes the
# cost evaluation very cheap, so a large number of group orders and
# connection sets can be searched. Orders of the form 2*G with G above the
# record half are targeted (the record 684 = 2*342 is AGL(1,19)-type).
# ----------------------------------------------------------------------------

_KNOWN_RECORD = {(6, 5): 684}


def _semidirect_orders(G):
    """All (m, k, r) with m*k = G, m >= 2, r a unit with r^k = 1 mod m."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Multiplication table and inverses of Z_m x| Z_k, element (a, b) coded as a*k + b."""
    G = m * k
    xs = np.arange(G, dtype=np.int64)
    a = xs // k
    b = xs % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    E = b[None, :]
    mt = ((A + pw[B] * C) % m) * k + (B + E) % k
    inv = np.argmax(mt == 0, axis=1)
    return G, mt.tolist(), inv.tolist()


def _cost(G, mt, inv, S, D, limit):
    """Unreached (vertex, source) pairs from A_e and B_e within distance D. Zero means valid."""
    N = 2 * G
    invS = [inv[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = mt[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = mt[u - G]
                    for t in invS:
                        v = row[t]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
        if total > limit:
            return total
    return total


def _search(G, d, D, mt, inv, rng, deadline):
    """Annealed swap search over d-subsets S of the group. Returns (S or None, cost)."""
    S = rng.sample(range(G), d)
    c = _cost(G, mt, inv, S, D, float("inf"))
    temp = 1.0
    while c > 0 and time.monotonic() < deadline:
        temp = max(0.05, temp * 0.9995)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        limit = c - temp * math.log(1.0 - rng.random())
        ct = _cost(G, mt, inv, T, D, limit)
        if ct <= limit:
            S, c = T, ct
    return (S if c == 0 else None), c


def _edges(G, mt, S):
    E = []
    for g in range(G):
        row = mt[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


def _schedule(lo_up, lo_down, lo_floor, hi):
    """Interleave group orders: upward from lo_up, downward from lo_down toward lo_floor."""
    order = []
    for i in range(400):
        if lo_up + i <= hi:
            order.append(lo_up + i)
        if lo_down - i >= lo_floor:
            order.append(lo_down - i)
    return order


def _bicayley_phase(d, D, schedule, rng, deadline, consider):
    for G in schedule:
        now = time.monotonic()
        if now >= deadline:
            break
        g_end = min(deadline, now + 2.0)
        groups = _semidirect_orders(G)
        rng.shuffle(groups)
        for (m, k, r) in groups[:4]:
            now = time.monotonic()
            if now >= g_end:
                break
            _, mt, inv = _tables(m, k, r)
            slice_end = min(g_end, time.monotonic() + 0.6)
            S, _ = _search(G, d, D, mt, inv, rng, slice_end)
            if S is not None:
                n, e = _edges(G, mt, S)
                consider(n, e)
                break


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    base_n, base_e = lib.haar_graph(d, range(d))
    state = {"n": base_n, "e": base_e}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, e
            return True
        return False

    moore = lib._moore_bound(d, D)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound return immediately.
    if state["n"] >= moore:
        return state["n"], list(state["e"])

    if D >= 3:
        known = _KNOWN_RECORD.get((d, D), 0)
        hi = moore // 2
        lo_floor = max(state["n"] // 2 + 1, d)
        if known:
            lo_up = max(known // 2 + 1, lo_floor)
            lo_down = max(known // 2, lo_floor)
        else:
            lo_up = lo_floor
            lo_down = lo_floor
        sched = _schedule(lo_up, lo_down, lo_floor, hi)
        _bicayley_phase(d, D, sched, rng, deadline, consider)

    if not lib.is_valid(state["n"], state["e"], d, D):
        return base_n, list(base_e)
    return state["n"], list(state["e"])
