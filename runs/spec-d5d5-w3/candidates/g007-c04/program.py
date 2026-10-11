import itertools
import math
import random
import time

import numpy as np

import lib

CHUNK = 2500          # annealing steps per chunk
MAX_FAILS = 6         # chunks without success before restoring the last good state
T_START = 1.0
T_END = 0.15

_BC = getattr(np, "bitwise_count", None)


# ----------------------------------------------------------------------------
# Structured baselines.
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


# ----------------------------------------------------------------------------
# Regular bipartite graphs searched by edge switches.
# Local labels: A-vertex a in 0..N-1, B-vertex b in 0..N-1.
# Unified labels: A-vertex a -> a, B-vertex b -> N + b.
# ----------------------------------------------------------------------------

def _identity_bits(N2):
    """Bitset rows: row v has only bit v set."""
    words = (N2 + 63) // 64
    R = np.zeros((N2, words), dtype=np.uint64)
    idx = np.arange(N2, dtype=np.int64)
    R[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    return R


def _pop(R):
    """Total number of set bits in the bitset array R."""
    if _BC is not None:
        return int(_BC(R).sum(dtype=np.int64))
    return int(np.unpackbits(R.view(np.uint8)).sum(dtype=np.int64))


def _rep(lst, old, new):
    lst[lst.index(old)] = new


class _Graph:
    """A d-regular bipartite graph on N + N vertices, kept as an edge list plus adjacency."""

    def __init__(self, d, D, N, E):
        self.d = d
        self.D = D
        self.N = N
        self.E = [list(e) for e in E]
        self._rebuild()

    def _rebuild(self):
        N = self.N
        nb = [[] for _ in range(2 * N)]
        S = set()
        for a, b in self.E:
            nb[a].append(N + b)
            nb[N + b].append(a)
            S.add(a * N + b)
        self.nb = nb
        self.S = S
        self.I0 = _identity_bits(2 * N)

    def cost(self):
        """Number of unordered vertex pairs at distance > D (zero means valid)."""
        arr = np.array(self.nb, dtype=np.int64)
        R = self.I0
        for _ in range(self.D):
            R = R | np.bitwise_or.reduce(R[arr], axis=1)
        N2 = 2 * self.N
        return (N2 * N2 - _pop(R)) // 2

    def _switch(self, i, j, a1, b1, a2, b2):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Caller ensures validity."""
        N = self.N
        self.E[i] = [a1, b2]
        self.E[j] = [a2, b1]
        self.S.discard(a1 * N + b1)
        self.S.discard(a2 * N + b2)
        self.S.add(a1 * N + b2)
        self.S.add(a2 * N + b1)
        nb = self.nb
        _rep(nb[a1], N + b1, N + b2)
        _rep(nb[N + b1], a1, a2)
        _rep(nb[a2], N + b2, N + b1)
        _rep(nb[N + b2], a2, a1)

    def anneal(self, rng, deadline, iters, t0, t1):
        """Simulated annealing over edge switches; returns the final cost."""
        N = self.N
        E = self.E
        M = len(E)
        cur = self.cost()
        for it in range(iters):
            if cur == 0:
                break
            if (it & 31) == 0 and time.monotonic() > deadline:
                break
            T = t0 * (t1 / t0) ** (it / iters)
            i = rng.randrange(M)
            j = rng.randrange(M)
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2:
                continue
            if (a1 * N + b2) in self.S or (a2 * N + b1) in self.S:
                continue
            self._switch(i, j, a1, b1, a2, b2)
            new = self.cost()
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                self._switch(i, j, a1, b2, a2, b1)
        return cur

    def insert(self, rng):
        """Add one A-vertex and one B-vertex, keeping regularity by rerouting d matched edges."""
        d, N = self.d, self.N
        E = self.E
        M = len(E)
        pick = None
        for _ in range(60):
            order = list(range(M))
            rng.shuffle(order)
            ua, ub, cand = set(), set(), []
            for i in order:
                a, b = E[i]
                if a in ua or b in ub:
                    continue
                ua.add(a)
                ub.add(b)
                cand.append(i)
                if len(cand) == d:
                    break
            if len(cand) == d:
                pick = cand
                break
        if pick is None:
            return False
        ps = set(pick)
        kept = [E[i] for i in range(M) if i not in ps]
        for i in pick:
            a, b = E[i]
            kept.append([N, b])   # new A-vertex to old B-vertex b
            kept.append([a, N])   # old A-vertex a to new B-vertex
        self.N = N + 1
        self.E = kept
        self._rebuild()
        return True

    def edges_out(self):
        N = self.N
        return 2 * N, [(a, N + b) for a, b in self.E]


def _initial_state(d, D):
    """Starting regular bipartite graph: GQ(d-1) incidence when available, else a Haar graph."""
    q = d - 1
    if D >= 4 and 2 <= q <= 8 and lib.is_prime_power(q):
        P_n, P_e = _gq_w(q)
        N = P_n // 2
        return N, [(u, v - N) for u, v in P_e]
    N = d
    return N, [(i, (i + s) % d) for i in range(d) for s in range(d)]


def _search(d, D, N, E, rng, deadline, consider):
    """Grow a regular bipartite graph one vertex pair at a time, repairing diameter by annealing."""
    g = _Graph(d, D, N, E)
    good_N, good_E = N, [list(e) for e in E]
    fails = 0
    while time.monotonic() < deadline:
        c = g.anneal(rng, deadline, CHUNK, T_START, T_END)
        if c == 0:
            n2, e2 = g.edges_out()
            consider(n2, e2)
            good_N = g.N
            good_E = [list(e) for e in g.E]
            fails = 0
            if time.monotonic() >= deadline:
                break
            if not g.insert(rng):
                break
        else:
            fails += 1
            if fails >= MAX_FAILS:
                g = _Graph(d, D, good_N, good_E)
                if not g.insert(rng):
                    break
                fails = 0


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # K_{d,d}: bipartite, degree d, diameter 2. Safe fallback.
    base_n, base_e = lib.haar_graph(d, range(d))
    if D == 2:
        return base_n, base_e

    best = {"n": base_n, "e": base_e}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"], best["e"] = n, e
            return True
        return False

    moore = lib.moore_bound(d, D)

    if D == 3:
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best["n"], best["e"]
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best["n"] < moore:
        try:
            N, E = _initial_state(d, D)
            _search(d, D, N, E, rng, deadline, consider)
        except Exception:
            pass

    n, e = best["n"], best["e"]
    if not lib.is_valid(n, e, d, D):
        n, e = base_n, base_e
    return n, e

