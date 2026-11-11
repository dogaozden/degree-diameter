"""Metacyclic voltage-lift search (pure Python + numpy) with a validated fallback chain.

Construction: a 2p-fibre bipartite lift over a metacyclic group Z_m x|_r Z_k of order N.
Base graph: d random perfect matchings between p A-vertices and p B-vertices (a d-regular
multigraph), and each dart carries a voltage in the group. Left multiplication is an
automorphism acting regularly on every fibre, so the diameter is at most D iff a BFS from
each of the 2p fibre identities reaches every vertex within D steps. Voltages are annealed
against that exact count, using vectorised numpy BFS. Orders are climbed adaptively from
the best valid graph so far. Every output is checked with lib.is_valid, and the fallbacks
are the algebraic starts and K_{d,d}, so the program always returns a valid graph.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

_GCACHE = {}


def _groups(N):
    """All metacyclic groups Z_m x|_r Z_k of order N as (m, k, r); r = 1 is the direct product."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    return out


def _group_list(N):
    if N not in _GCACHE:
        _GCACHE[N] = _groups(N)
    return _GCACHE[N]


class _Group:
    """Metacyclic group with element a*k+b for (a, b); (a,b)(c,e) = (a + r^b c, b + e)."""

    def __init__(self, m, k, r):
        self.m, self.k = m, k
        self.rp = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)

    def mul_vec(self, x, g):
        """Elementwise x * g for an int64 array x and a scalar element g."""
        k, m = self.k, self.m
        a = x // k
        b = x % k
        c, e = divmod(g, k)
        return ((a + self.rp[b] * c) % m) * k + (b + e) % k


def _edges(grp, p, N, darts):
    """Undirected edge arrays of the lift. A-fibre i occupies i*N.., B-fibre j occupies (p+j)*N.."""
    x = np.arange(N, dtype=np.int64)
    us, vs = [], []
    for i, j, g in darts:
        us.append(i * N + x)
        vs.append((p + j) * N + grp.mul_vec(x, g))
    return np.concatenate(us), np.concatenate(vs)


def _bad(grp, p, N, darts, D):
    """Number of (fibre identity, vertex) pairs at distance > D. Zero iff diameter <= D."""
    u, v = _edges(grp, p, N, darts)
    src = np.concatenate([u, v])
    dst = np.concatenate([v, u])
    nv = 2 * p * N
    bad = 0
    for f in range(2 * p):
        seen = np.zeros(nv, dtype=bool)
        seen[f * N] = True
        front = seen.copy()
        for _ in range(D):
            hit = np.zeros(nv, dtype=bool)
            hit[dst[front[src]]] = True
            hit &= ~seen
            if not hit.any():
                break
            seen |= hit
            front = hit
        bad += nv - int(seen.sum())
    return bad


def _ok(darts, t, g):
    """True if voltage g on dart t does not duplicate another dart's voltage on the same fibre pair."""
    i, j, _ = darts[t]
    for s, (a, b, h) in enumerate(darts):
        if s != t and a == i and b == j and h == g:
            return False
    return True


def _random_darts(rng, p, N, d):
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            darts.append([i, perm[i], -1])
    for t in range(len(darts)):
        while True:
            g = rng.randrange(N)
            if _ok(darts, t, g):
                break
        darts[t][2] = g
    return darts


def _anneal(rng, grp, p, N, D, darts, until, iters):
    """Anneal voltages to zero bad pairs. Returns the final bad count; darts is updated in place."""
    cur = _bad(grp, p, N, darts, D)
    T = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > until:
            break
        t = rng.randrange(len(darts))
        g = rng.randrange(N)
        old = darts[t][2]
        if g == old or not _ok(darts, t, g):
            continue
        darts[t][2] = g
        c = _bad(grp, p, N, darts, D)
        if c <= cur or rng.random() < math.exp((cur - c) / T):
            cur = c
        else:
            darts[t][2] = old
        T = max(0.05, T * 0.997)
    return cur


def _to_graph(grp, p, N, darts):
    u, v = _edges(grp, p, N, darts)
    return 2 * p * N, list(zip(u.tolist(), v.tolist()))


def _attempt(rng, p, N, d, D, until):
    """Random restarts (group, base, voltages) at order N until the slice ends. Returns a graph or None."""
    groups = _group_list(N)
    nonab = [g for g in groups if g[0] > 1 and g[2] != 1]
    while time.monotonic() < until:
        pool = nonab if (nonab and rng.random() < 0.85) else groups
        m, k, r = rng.choice(pool)
        grp = _Group(m, k, r)
        darts = _random_darts(rng, p, N, d)
        bad = _anneal(rng, grp, p, N, D, darts, until, 1500)
        if bad == 0:
            return _to_graph(grp, p, N, darts)
    return None


def _pick_order(rng, p, N0, d, moore):
    """Choose a group order near N0, preferring orders that admit nonabelian metacyclic groups."""
    lo = max(N0, d)
    cands = []
    for N in range(lo, lo + 40):
        if 2 * p * N > moore:
            break
        if any(g[0] > 1 and g[2] != 1 for g in _group_list(N)):
            cands.append(N)
            if len(cands) >= 4:
                break
    if cands:
        return rng.choice(cands)
    if 2 * p * lo > moore:
        return None
    return lo


def _search(d, D, rng, deadline, best, moore):
    best_n = best[0]
    step = 2
    while time.monotonic() < deadline:
        if best_n + 2 > moore:
            break
        p = 1 if rng.random() < 0.6 else 2
        target = best_n + step
        N0 = -(-target // (2 * p))
        N = _pick_order(rng, p, N0, d, moore)
        if N is None:
            p = 1
            N0 = -(-target // 2)
            N = _pick_order(rng, p, N0, d, moore)
            if N is None:
                step = max(2, step // 2)
                continue
        remaining = deadline - time.monotonic()
        if remaining <= 0.2:
            break
        slice_len = min(remaining, max(3.0, remaining / 4))
        until = time.monotonic() + slice_len
        g = _attempt(rng, p, N, d, D, until)
        if g is not None and g[0] > best_n and lib.is_valid(g[0], g[1], d, D):
            best = g
            best_n = g[0]
            step = min(step * 2, 1 << 12)
        else:
            step = max(2, step // 2)
    return best


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    for cand in known_starts(d, D):
        n, e = cand
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = cand
        except Exception:
            pass

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    deadline = t0 + max(0.5, 0.85 * time_limit - 1.5)
    rng = random.Random(seed * 1000003 + d * 101 + D)
    try:
        cand = _search(d, D, rng, deadline, best, moore)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
