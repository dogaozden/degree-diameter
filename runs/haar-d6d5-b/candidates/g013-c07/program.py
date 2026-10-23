"""Voltage-lift search for the d=6, D=5 target, with a verified Haar fallback.

Construction: a 2+2 base bipartite multigraph (A0, A1 | B0, B1), each vertex of degree 6, with dart
multiplicities [[t, 6-t], [6-t, t]].  Over a group G of order N, dart (i, j, s) joins (i, g) to (j, s*g),
so the lift has 4N vertices and is 6-regular and bipartite.  Right multiplication is an automorphism, so
diameter <= 5 iff the radius-5 balls around (0, e) and (1, e) cover everything.  The cost is the number of
uncovered vertices from those two sources, computed by a numpy BFS.  Annealing over darts runs round-robin
across many non-abelian groups of order 166..261 (and Heisenberg(7), order 343).  Any cost-0 lift is checked
with lib.is_valid.  If nothing beats the fallback, the verified Haar graph of order 660 is returned.
"""
import itertools
import math
import time
from math import gcd

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5
PATIENCE = 2500
SLICE = 0.35


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> index a*k + j.  Needs lam^k = 1 mod m."""
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
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sc = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sc, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3, identity first."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def build_group(spec):
    if spec[0] == 'meta':
        return group_meta(spec[1], spec[2], spec[3])
    return group_heis(spec[1])


# ------------------------------------------------------------------------- lift search

def _uncovered_from(nb, src):
    """Number of vertices not within DIAM of vertex src in the graph with neighbour table nb."""
    n = nb.shape[0]
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(DIAM):
        cand = nb[frontier].ravel()
        cand = cand[~seen[cand]]
        if cand.size == 0:
            break
        cand = np.unique(cand)
        seen[cand] = True
        frontier = cand
    return n - int(seen.sum())


class Lift:
    """State: dart sets S[i][j] (subsets of the group) with sizes M[i][j]; cost 0 means a valid lift."""

    def __init__(self, spec, t, rng):
        MT, inv = build_group(spec)
        self.MT = MT.astype(np.int64)
        self.inv = inv.astype(np.int64)
        self.N = self.MT.shape[0]
        self.rng = rng
        self.M = [[t, DEG - t], [DEG - t, t]]
        self.reset()
        self.best = self.cur
        self.best_S = self._copy()

    def _copy(self):
        return [[a.copy() for a in row] for row in self.S]

    def reset(self):
        N = self.N
        self.S = [[self.rng.choice(N, self.M[i][j], replace=False).astype(np.int64)
                   for j in range(2)] for i in range(2)]
        self.cur = self.cost()
        self.stall = 0

    def neighbours(self, S):
        N, MT, inv = self.N, self.MT, self.inv
        nb = np.empty((4 * N, DEG), dtype=np.int64)
        for i in range(2):
            nb[i * N:(i + 1) * N] = np.concatenate([MT[S[i][j]].T + (2 + j) * N for j in range(2)], axis=1)
        for j in range(2):
            nb[(2 + j) * N:(3 + j) * N] = np.concatenate([MT[inv[S[i][j]]].T + i * N for i in range(2)], axis=1)
        return nb

    def cost(self):
        nb = self.neighbours(self.S)
        return _uncovered_from(nb, 0) + _uncovered_from(nb, self.N)

    def graph(self, S):
        nb = self.neighbours(S)
        A = np.repeat(np.arange(2 * self.N), DEG)
        B = nb[:2 * self.N].ravel()
        return 4 * self.N, list(zip(A.tolist(), B.tolist()))

    def step(self):
        rng = self.rng
        i = int(rng.integers(2))
        j = int(rng.integers(2))
        s = self.S[i][j]
        x = int(rng.integers(self.N))
        if np.any(s == x):
            return
        k = int(rng.integers(s.size))
        new = s.copy()
        new[k] = x
        old = s
        self.S[i][j] = new
        c = self.cost()
        delta = c - self.cur
        if delta <= 0 or rng.random() < math.exp(-delta / 1.2):
            self.cur = c
            if c < self.best:
                self.best = c
                self.best_S = self._copy()
                self.stall = 0
                return
        else:
            self.S[i][j] = old
        self.stall += 1
        if self.stall > PATIENCE:
            self.reset()

    def run(self, deadline):
        while time.monotonic() < deadline:
            for _ in range(40):
                if self.cur == 0:
                    return True
                self.step()
        return self.cur == 0


def candidate_list():
    """(group order, group spec, pattern parameter t) entries, ordered by group order."""
    cands = []
    for N in range(166, 262):
        found = []
        for m in range(2, N):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    found.append(('meta', m, k, lam))
        step = max(1, len(found) // 3)
        for spec in found[::step][:3]:
            cands.append((N, spec, 3))
    cands.sort(key=lambda c: c[0])
    cands.append((343, ('heis', 7), 3))
    cands += [(N, spec, 2) for (N, spec, _) in cands[::3]]
    return cands[:90]


def lift_search(rng, deadline, best_n):
    cands = candidate_list()
    states = [None] * len(cands)
    finished = [False] * len(cands)
    best = None
    idx = 0
    while time.monotonic() < deadline:
        live = [c for c in range(len(cands)) if not finished[c] and 4 * cands[c][0] > best_n]
        if not live:
            break
        ci = live[idx % len(live)]
        idx += 1
        _, spec, t = cands[ci]
        if states[ci] is None:
            try:
                states[ci] = Lift(spec, t, rng)
            except Exception:
                finished[ci] = True
                continue
        st = states[ci]
        end = min(deadline, time.monotonic() + SLICE)
        try:
            ok = st.run(end)
        except Exception:
            finished[ci] = True
            continue
        if ok:
            finished[ci] = True
            n, edges = st.graph(st.best_S)
            if n > best_n and lib.is_valid(n, edges, DEG, DIAM):
                best = (n, edges)
                best_n = n
    return best


# ---------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def fallback_graph():
    MT, _ = group_meta(33, 10, 26)
    return haar_edges(MT, [0, 179, 116, 180, 47, 306])


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    best = None
    try:
        n, edges = fallback_graph()
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        best = None
    try:
        got = lift_search(rng, deadline, best[0] if best else 0)
        if got is not None and (best is None or got[0] > best[0]):
            best = got
    except Exception:
        pass
    return best if best is not None else trivial(d, D)
