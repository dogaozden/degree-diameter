import itertools
import math
import random
import time

import numpy as np

import lib


_PEN = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Exact / safe baseline families (fast, return immediately when they are records).
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
# Bi-Cayley lifts over Z_m x| Z_k2, searched by iterated local search.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{j,g*s}.
# Each layer is a permutation of blocks, so every vertex has degree exactly d.
# Left multiplication is an automorphism, so distances from the 2k block
# representatives determine the diameter.
#
# Search style (different from annealing): for each slot, scan a random sample
# of candidate voltages and take the best one (ties allowed as plateau moves),
# and kick from the best-so-far state when stuck.
# ----------------------------------------------------------------------------

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


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
    N = nbr.shape[1]
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
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


class _Lift:
    """A bi-Cayley lift state: layers (block permutations) and voltages, with neighbour table."""

    def __init__(self, k, G, Ts, Invs, d, rng):
        self.k, self.G, self.Ts, self.Invs, self.d = k, G, Ts, Invs, d
        self.N = 2 * k * G
        self.layers = [rng.sample(range(k), k) for _ in range(d)]
        self.S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        self.nbr = np.empty((d, self.N), dtype=np.int64)
        for l in range(d):
            for i in range(k):
                self.refresh(l, i)

    def refresh(self, l, i):
        k, G = self.k, self.G
        j = self.layers[l][i]
        s = self.S[l][i]
        self.nbr[l, i * G:(i + 1) * G] = (k + j) * G + self.Ts[s]
        self.nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + self.Invs[s]

    def refresh_all(self):
        for l in range(self.d):
            for i in range(self.k):
                self.refresh(l, i)

    def dup(self):
        keys = [(i, self.layers[l][i], self.S[l][i]) for l in range(self.d) for i in range(self.k)]
        return len(keys) - len(set(keys))

    def cost(self, D):
        reach = _reach(self.k, self.G, D, self.nbr, self.d)
        return _unreached(self.k, self.N, reach) + _PEN * self.dup()

    def state(self):
        return ([row[:] for row in self.layers], [row[:] for row in self.S])

    def load(self, st):
        self.layers = [row[:] for row in st[0]]
        self.S = [row[:] for row in st[1]]
        self.refresh_all()

    def edges(self):
        e = set()
        for l in range(self.d):
            for u in range(self.N):
                v = int(self.nbr[l, u])
                e.add((u, v) if u < v else (v, u))
        return self.N, sorted(e)


def _ils(lift, D, rng, deadline):
    """Iterated local search on voltages. Returns True when the lift has cost 0."""
    k, G, d = lift.k, lift.G, lift.d
    cur = lift.cost(D)
    best = cur
    best_state = lift.state()
    stall = 0
    while cur > 0 and time.monotonic() < deadline:
        slots = [(l, i) for l in range(d) for i in range(k)]
        rng.shuffle(slots)
        before = cur
        for l, i in slots:
            if cur == 0 or time.monotonic() > deadline:
                break
            old = lift.S[l][i]
            bv, bc = old, None
            for v in rng.sample(range(G), min(G, 40)):
                if v == old:
                    continue
                lift.S[l][i] = v
                lift.refresh(l, i)
                c = lift.cost(D)
                if bc is None or c < bc:
                    bc, bv = c, v
                if c == 0:
                    break
            if bc is not None and bc <= cur:
                lift.S[l][i] = bv
                cur = bc
            else:
                lift.S[l][i] = old
            lift.refresh(l, i)
            if cur < best:
                best = cur
                best_state = lift.state()
            if cur == 0:
                break
        stall = 0 if cur < before else stall + 1
        if cur > 0 and stall >= 3:
            if rng.random() < 0.5:
                lift.load(best_state)
            for _ in range(2):
                l, i = rng.randrange(d), rng.randrange(k)
                lift.S[l][i] = rng.randrange(G)
                lift.refresh(l, i)
            if rng.random() < 0.3 and k >= 2:
                l = rng.randrange(d)
                i1, i2 = rng.sample(range(k), 2)
                lift.layers[l][i1], lift.layers[l][i2] = lift.layers[l][i2], lift.layers[l][i1]
                lift.refresh(l, i1)
                lift.refresh(l, i2)
            cur = lift.cost(D)
            stall = 0
    return cur == 0


def _sample_group(G, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order exactly G, or None."""
    if G < 2:
        return None
    if rng.random() < 0.35:
        k2 = 1
    else:
        divs = [t for t in range(2, min(G, 40) + 1) if G % t == 0]
        if not divs:
            return None
        k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1:
        return (G, 1, 1)
    if m < 2:
        return None
    cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not cands:
        return None
    return (m, k2, rng.choice(cands))


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

    # Safe fallback: K_{d,d} has diameter 2.
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

    # Lift search: target group orders just above the current record-to-beat.
    ks = [1, 1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline - 0.5:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        span = max(2, lo // 60)
        G = lo + rng.randrange(span)
        if G > 1500:
            continue
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        m, k2, r = grp
        G2, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G2 <= best_n:
            continue
        remaining = deadline - time.monotonic()
        slice_end = time.monotonic() + min(remaining, 8.0)
        lift = _Lift(k, G2, Ts, Invs, d, rng)
        if _ils(lift, D, rng, slice_end):
            n, e = lift.edges()
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
