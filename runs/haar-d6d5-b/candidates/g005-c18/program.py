"""Bi-Cayley (two-orbit) search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and four connection sets S_ij (i, j in {0, 1}) of sizes
a, 6-a, 6-a, a (a in {2, 3, 4}), so every vertex has degree 6.  Vertices are A_i(g) and B_j(g) for g in G,
with edges A_i(g) ~ B_j(g*s) for s in S_ij.  Left multiplication by any h in G is an automorphism, so each of the
four orbits is vertex-transitive and the diameter is at most 5 iff BFS (radius 5) from the four base vertices
A_0(e), A_1(e), B_0(e), B_1(e) reaches every vertex.  The graph has 4N vertices, so N >= 172 beats the record 684.

NEW IN THIS VERSION.
  * Round-robin search over many non-abelian groups at once.  Each group keeps its own annealing state, and the
    runners advance in short turns, so no group is starved by a long run on another group.
  * Group-aware move proposals.  Besides a uniform random replacement, a slot can take a product s1*s2 of two
    current set elements, or the inverse of one.  These moves keep the new element inside the subgroup the
    current sets generate, which is where cost-0 configurations tend to lie.
  * Best-of-K move selection (K = 4) at each annealing step, with a random temperature per restart.
  * Groups whose order cannot beat the best graph found so far are dropped.

COST(S) = total number of vertices not reached within 5 steps from the four base vertices (0 = valid).
Every returned graph is checked with lib.is_valid.  If nothing is found in the budget, the valid Haar graph of
order 660 (checked at run time) or a trivial valid graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 172   # 4 * 172 = 688 > 684 (record)


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- Haar fallback helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------- bi-Cayley graph and cost

def _nbr(MT, inv, N, S):
    """Neighbour array (4N x DEG).  Orbits: A_0 = 0..N-1, A_1 = N..2N-1, B_0 = 2N..3N-1, B_1 = 3N..4N-1.
    A_i(g) ~ B_j(g*s) for s in S[(i, j)]."""
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, DEG), dtype=np.int64)
    for i in (0, 1):
        c = 0
        for j in (0, 1):
            for s in S[(i, j)]:
                nbr[i * N:(i + 1) * N, c] = (2 + j) * N + MT[g, s]
                c += 1
    for j in (0, 1):
        c = 0
        for i in (0, 1):
            for s in S[(i, j)]:
                nbr[(2 + j) * N:(3 + j) * N, c] = i * N + MT[g, inv[s]]
                c += 1
    return nbr


def _cost(nbr, N):
    """Vertices not reached within DIAM steps from the four base vertices (0 means diameter <= DIAM)."""
    n = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nbr[fr].ravel()
            nx = np.unique(nx[~seen[nx]])
            if nx.size == 0:
                break
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


# ------------------------------------------------------------------------- candidate groups

def _candidates():
    """Non-abelian metacyclic groups of order in [MIN_N, 200] (two actions per (m, k)), plus Heis(3) x Z_7 (order 189)."""
    out = []
    for NN in range(MIN_N, 201):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append(("meta", m, k, lam))
                    cnt += 1
                    if cnt >= 2:
                        break
    out.append(("heis", 3, 7, 0))

    def order(c):
        return c[1] * c[2] if c[0] == "meta" else 27 * c[2]
    out.sort(key=order)
    return out


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_times_cyclic(group_heis(c[1]), c[2])


# ----------------------------------------------------------------------- per-group annealing runner

class _Runner:
    """Annealing state for one group.  step() advances it by a number of moves and returns a checked graph or None."""

    def __init__(self, c, rng):
        self.rng = rng
        self.MT, self.inv = _make(c)
        self.N = int(self.MT.shape[0])
        self.done = False
        self._restart()

    def _restart(self):
        rng, N = self.rng, self.N
        a = int(rng.choice([2, 3, 3, 4]))
        self.sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        self.keys = list(self.sizes)
        self.S = {k: rng.choice(N, size=self.sizes[k], replace=False).astype(np.int64) for k in self.keys}
        self.cur = _cost(_nbr(self.MT, self.inv, N, self.S), N)
        self.stall = 0
        self.T = float(rng.choice([0.4, 0.6, 0.9]))

    def _propose(self):
        """Group-aware move: uniform element, product of two current elements, or inverse of a current element."""
        rng, S, keys = self.rng, self.S, self.keys
        key = keys[int(rng.integers(4))]
        pos = int(rng.integers(self.sizes[key]))
        allel = np.concatenate([S[k] for k in keys])
        r = rng.random()
        if r < 0.5:
            x = int(rng.integers(self.N))
        elif r < 0.75:
            x = int(self.MT[int(rng.choice(allel)), int(rng.choice(allel))])
        else:
            x = int(self.inv[int(rng.choice(allel))])
        return key, pos, x

    def _finish(self):
        n = 4 * self.N
        nbr = _nbr(self.MT, self.inv, self.N, self.S)
        edges = [(u, int(v)) for u in range(2 * self.N) for v in nbr[u]]
        if lib.is_valid(n, edges, DEG, DIAM):
            return n, edges
        return None

    def step(self, moves):
        for _ in range(moves):
            if self.cur == 0:
                res = self._finish()
                if res is not None:
                    self.done = True
                    return res
                self._restart()
                continue
            # Best-of-K proposals.
            best = None
            for _ in range(4):
                key, pos, x = self._propose()
                if x in self.S[key]:
                    continue
                newS = dict(self.S)
                arr = self.S[key].copy()
                arr[pos] = x
                newS[key] = arr
                c = _cost(_nbr(self.MT, self.inv, self.N, newS), self.N)
                if best is None or c < best[0]:
                    best = (c, newS)
            if best is None:
                self.stall += 1
            else:
                c, newS = best
                delta = c - self.cur
                if delta <= 0 or self.rng.random() < math.exp(-delta / self.T):
                    self.S, self.cur = newS, c
                    self.stall = 0 if delta < 0 else self.stall + 1
                else:
                    self.stall += 1
            if self.stall > 3000:
                self._restart()
        return None


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    runners = []
    for c in _candidates():
        if time.monotonic() >= deadline:
            break
        try:
            runners.append(_Runner(c, rng))
        except Exception:
            continue

    best = None
    while runners and time.monotonic() < deadline:
        for r in list(runners):
            if time.monotonic() >= deadline:
                break
            try:
                res = r.step(40)
            except Exception:
                runners.remove(r)
                continue
            if res is not None:
                if best is None or res[0] > best[0]:
                    best = res
                runners.remove(r)
        # Drop groups that cannot beat the best graph found so far.
        if best is not None:
            runners = [r for r in runners if 4 * r.N > best[0]]

    if best is not None:
        return best
    return _fallback(d, D)
