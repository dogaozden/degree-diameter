import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact small families (kept from the parent for D = 3 and D = 4).
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
# Different search space from the parent: a bi-Cayley lift over Z_m x|_r Z_k2
# with base size k and d "layers". Every layer is a bijection between A-blocks
# and B-blocks, carrying a voltage. The whole structure is vertex-regular within
# each block, so the diameter check needs only the k block identities as BFS
# sources (one bitmask sweep), not per-vertex searches.
#
# Group orders are chosen so 2*k*|G| is just above the current best, and
# simulated annealing over voltages and layer permutations tries to close the
# diameter gap. Every success is re-verified with lib.is_valid before use.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _group_options(G, rng):
    """Candidate (m, k2, r) for Z_m x|_r Z_k2 with m * k2 = G, shuffled."""
    opts = []
    for gk in range(1, G + 1):
        if G % gk:
            continue
        gm = G // gk
        if gm < 2:
            continue
        if gk == 1:
            opts.append((gm, 1, 1))
            continue
        rs = [r for r in range(1, gm)
              if math.gcd(r, gm) == 1 and pow(r, gk, gm) == 1 % gm]
        if not rs:
            continue
        if len(rs) > 6:
            rs = rng.sample(rs, 6)
        for r in rs:
            opts.append((gm, gk, r))
    rng.shuffle(opts)
    return opts


class _Lift:
    """Bi-Cayley lift: A_{i,g} ~ B_{p_l(i), g * v_{l,i}} for each layer l."""

    def __init__(self, d, D, k, gm, gk, gr, rng):
        self.d, self.D, self.k = d, D, k
        self.gm, self.gk = gm, gk
        G = gm * gk
        self.G = G
        self.N = 2 * k * G
        xs = np.arange(G, dtype=np.int64)
        self.xa = xs // gk
        self.xb = xs % gk
        pw = np.array([pow(gr, t, gm) for t in range(gk)], dtype=np.int64)
        self.pw = pw
        self.pwb = pw[self.xb]
        self.ok = True
        self.p = [rng.sample(range(k), k) for _ in range(d)]
        self.v = [[0] * k for _ in range(d)]
        used = [set() for _ in range(k)]
        for l in range(d):
            for i in range(k):
                j = self.p[l][i]
                s = None
                for _ in range(20000):
                    cand = rng.randrange(G)
                    if (j, cand) not in used[i]:
                        s = cand
                        break
                if s is None:
                    self.ok = False
                    return
                used[i].add((j, s))
                self.v[l][i] = s
        self.nbr = np.empty((d, self.N), dtype=np.int64)
        for l in range(d):
            self._set_layer(l)

    def _mul(self, c, e):
        """Array of x * (c, e) over all group elements x (index a*gk + b)."""
        return ((self.xa + self.pwb * c) % self.gm) * self.gk + (self.xb + e) % self.gk

    def _set_layer(self, l):
        G, k, gk = self.G, self.k, self.gk
        row = self.nbr[l]
        for i in range(k):
            j = self.p[l][i]
            s = self.v[l][i]
            c, e = divmod(s, gk)
            row[i * G:(i + 1) * G] = (k + j) * G + self._mul(c, e)
            # Inverse of (c, e) in Z_m x|_r Z_k is (-r^{-e} c, -e).
            nb = (-e) % gk
            nc = (-int(self.pw[nb]) * c) % self.gm
            row[(k + j) * G:(k + j + 1) * G] = i * G + self._mul(nc, nb)

    def _dup_free(self, i):
        keys = {(self.p[l][i], self.v[l][i]) for l in range(self.d)}
        return len(keys) == self.d

    def _cost(self):
        """Number of unreached (block identity, vertex) pairs after D rounds."""
        k, G, N = self.k, self.G, self.N
        reach = np.zeros(N, dtype=np.int64)
        for b in range(2 * k):
            reach[b * G] = 1 << b
        nbr = self.nbr
        for _ in range(self.D):
            new = reach.copy()
            for l in range(self.d):
                new |= reach[nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        return 2 * k * N - int(_POP8[reach].sum())

    def anneal(self, deadline, rng):
        """Simulated annealing over voltages and layer swaps. True when cost reaches 0."""
        cur = self._cost()
        if cur == 0:
            return True
        c0 = float(cur)
        t0 = time.monotonic()
        span = max(1e-3, deadline - t0)
        k, d = self.k, self.d
        while cur > 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / span
            temp = max(0.3, 0.01 * c0 * (1.0 - frac))

            if k >= 2 and rng.random() < 0.2:
                # Layer-swap move: exchange B-targets of two A-blocks in one layer.
                l = rng.randrange(d)
                i1, i2 = rng.sample(range(k), 2)
                pl = self.p[l]
                pl[i1], pl[i2] = pl[i2], pl[i1]
                if not (self._dup_free(i1) and self._dup_free(i2)):
                    pl[i1], pl[i2] = pl[i2], pl[i1]
                    continue
                self._set_layer(l)
                nc = self._cost()
                if nc <= cur or rng.random() < math.exp(-(nc - cur) / temp):
                    cur = nc
                else:
                    pl[i1], pl[i2] = pl[i2], pl[i1]
                    self._set_layer(l)
                continue

            # Voltage move.
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = self.v[l][i]
            new = rng.randrange(self.G)
            if new == old:
                continue
            self.v[l][i] = new
            if not self._dup_free(i):
                self.v[l][i] = old
                continue
            self._set_layer(l)
            nc = self._cost()
            if nc <= cur or rng.random() < math.exp(-(nc - cur) / temp):
                cur = nc
            else:
                self.v[l][i] = old
                self._set_layer(l)
        return cur == 0

    def edges(self):
        us = np.arange(self.N, dtype=np.int64)
        out = set()
        for l in range(self.d):
            vs = self.nbr[l]
            a = np.minimum(us, vs)
            b = np.maximum(us, vs)
            out.update(zip(a.tolist(), b.tolist()))
        return self.N, sorted(out)


# ----------------------------------------------------------------------------
# Entry point.
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

    if D <= 2:
        return best

    # Main search: round-robin over base sizes k, each aiming just above best_n.
    ks = (1, 2, 3, 4)
    target = {k: 0 for k in ks}
    slice_len = max(1.0, budget / 8.0)

    while time.monotonic() < deadline - 0.5:
        for k in ks:
            now = time.monotonic()
            if now > deadline - 0.5:
                break
            G = max(target[k], best_n // (2 * k) + 1, d, 2)
            target[k] = G
            opts = _group_options(G, rng)
            if not opts:
                target[k] = G + 1
                continue
            gm, gk, gr = rng.choice(opts)
            slice_end = min(deadline, now + slice_len)
            eng = _Lift(d, D, k, gm, gk, gr, rng)
            if not eng.ok:
                continue
            if eng.anneal(slice_end, rng):
                n, e = eng.edges()
                consider(n, e)
                target[k] = G + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
