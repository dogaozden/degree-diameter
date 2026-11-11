"""Haar-graph annealing over non-abelian matrix groups for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  For a finite group G with multiplication table MT and a connection set S of d distinct elements,
the Haar graph has vertices A_g and B_g (g in G) and edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular
and has 2|G| vertices.  Its diameter is at most 5 whenever (S^-1 S)^2 = G and (S S^-1)^2 = G.  So the search
minimises cost(S) = (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|), and a zero-cost S gives a valid graph.

GROUPS (this is the change from the parent's metacyclic voltage search).  Haar graphs over groups of order
2001 or more beat the record of 4000:
  * PGL(2,13) and SL(2,13), each of order 2184 (so 4368 vertices)
  * AGL(1,13) x Z_13 (order 2028) and AGL(1,11) x Z_19 (order 2090)
  * two random non-abelian metacyclic groups of order 2001..2100

SEARCH.  Round-robin simulated annealing over the groups, with single-slot replacements, Metropolis acceptance and
restarts.  Every zero-cost set is checked with lib.is_valid before it is accepted.

SAFETY.  The parent's valid Haar graph (3582 vertices) is built and verified first and is the fallback, so the
output is never worse than the parent's.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
RESTART = 20000

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def _matrix_group(p, keep, normalize):
    """Group of 2x2 matrices over GF(p) selected by keep(a,b,c,d,p); projective if normalize.

    Returns (N, MT, inv, e) with MT[x, y] = index of x*y and e the identity index.
    """
    arr = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    E = arr[keep(arr[:, 0], arr[:, 1], arr[:, 2], arr[:, 3], p)]
    if normalize:
        f = np.argmax(E != 0, axis=1)
        lead = E[np.arange(len(E)), f]
        E = E[lead == 1]
    N = len(E)

    def key(X):
        return ((X[..., 0] * p + X[..., 1]) * p + X[..., 2]) * p + X[..., 3]

    keymap = np.full(p ** 4, -1, dtype=np.int64)
    keymap[key(E)] = np.arange(N)
    invp = np.zeros(p, dtype=np.int64)
    for x in range(1, p):
        invp[x] = pow(x, p - 2, p)
    a2, b2, c2, d2 = E[:, 0], E[:, 1], E[:, 2], E[:, 3]
    MT = np.empty((N, N), dtype=np.int32)
    h = 32
    for lo in range(0, N, h):
        hi = min(N, lo + h)
        X = E[lo:hi]
        a1 = X[:, 0, None]
        b1 = X[:, 1, None]
        c1 = X[:, 2, None]
        d1 = X[:, 3, None]
        Z = np.stack([(a1 * a2[None] + b1 * c2[None]) % p,
                      (a1 * b2[None] + b1 * d2[None]) % p,
                      (c1 * a2[None] + d1 * c2[None]) % p,
                      (c1 * b2[None] + d1 * d2[None]) % p], axis=-1)
        if normalize:
            f = np.argmax(Z != 0, axis=2)
            lead = np.take_along_axis(Z, f[..., None], axis=2)[..., 0]
            Z = Z * invp[lead][..., None] % p
        MT[lo:hi] = keymap[key(Z)]
    if (MT < 0).any():
        raise ValueError("group not closed")
    e = int(keymap[p ** 3 + 1])
    inv = np.argmax(MT == e, axis=1).astype(np.int64)
    return N, MT, inv, e


def _times_cyclic(T, k):
    """Direct product of a group table with Z_k; element (x, c) -> x*k + c."""
    N1, MT1, _, e1 = T
    N = N1 * k
    X = np.arange(N)
    x = X // k
    c = X % k
    MT = (MT1[x[:, None], x[None, :]].astype(np.int64) * k + (c[:, None] + c[None, :]) % k).astype(np.int32)
    e = e1 * k
    inv = np.argmax(MT == e, axis=1).astype(np.int64)
    return N, MT, inv, e


def _meta(m, k, r):
    MT, inv = group_table(m, k, r)
    return m * k, MT, inv, 0


def _meta_triples(rng, count):
    """Sample (m, k, r) with m*k in [2001, 2100] giving non-abelian metacyclic groups."""
    out = []
    tries = 0
    while len(out) < count and tries < 400:
        tries += 1
        N = int(rng.integers(2001, 2101))
        divs = [m for m in range(2, N // 2 + 1) if N % m == 0]
        if not divs:
            continue
        m = divs[int(rng.integers(len(divs)))]
        k = N // m
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            out.append((m, k, rs[int(rng.integers(len(rs)))]))
    return out


def _group_makers(rng):
    pgl_keep = lambda a, b, c, d, p: (a * d - b * c) % p != 0
    sl_keep = lambda a, b, c, d, p: (a * d - b * c) % p == 1
    agl_keep = lambda a, b, c, d, p: (a != 0) & (c == 0) & (d == 1)
    makers = [
        lambda: _matrix_group(13, pgl_keep, True),
        lambda: _matrix_group(13, sl_keep, False),
        lambda: _times_cyclic(_matrix_group(13, agl_keep, False), 13),
        lambda: _times_cyclic(_matrix_group(11, agl_keep, False), 19),
    ]
    for m, k, r in _meta_triples(rng, 2):
        makers.append(lambda m=m, k=k, r=r: _meta(m, k, r))
    return makers


# ------------------------------------------------------------------------------ search

def haar_edges(MT, S, N):
    """Haar graph edges: A-vertex g is g, B-vertex h is N + h; A_g ~ B_{s*g}."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        edges.extend(zip(ar.tolist(), (N + MT[int(s)].astype(np.int64)).tolist()))
    return edges


class Chain:
    """Simulated annealing over connection sets S of size d in one group."""

    def __init__(self, N, MT, inv, d, rng):
        self.N = N
        self.MT = MT
        self.inv = inv
        self.d = d
        self.rng = rng
        self.reset()

    def _uncovered(self, X):
        mark = np.zeros(self.N, dtype=bool)
        mark[X] = True
        return self.N - int(np.count_nonzero(mark))

    def cost(self, S):
        MT = self.MT
        iS = self.inv[S]
        A = np.unique(MT[iS[:, None], S[None, :]].ravel())
        c1 = self._uncovered(MT[A[:, None], A[None, :]].ravel())
        B = np.unique(MT[S[:, None], iS[None, :]].ravel())
        c2 = self._uncovered(MT[B[:, None], B[None, :]].ravel())
        return c1 + c2

    def reset(self):
        self.S = self.rng.choice(self.N, self.d, replace=False).astype(np.int64)
        self.cur = self.cost(self.S)
        self.age = 0

    def run(self, steps):
        """Run up to `steps` moves; return a zero-cost S (as int array) if found, else None."""
        for _ in range(steps):
            if self.cur == 0:
                return self.S.copy()
            self.age += 1
            if self.age > RESTART:
                self.reset()
                continue
            t = int(self.rng.integers(self.d))
            g = int(self.rng.integers(self.N))
            if np.any(self.S == g):
                continue
            S2 = self.S.copy()
            S2[t] = g
            c2 = self.cost(S2)
            temp = 0.25 + 1.5 * (1.0 - self.age / RESTART)
            if c2 <= self.cur or self.rng.random() < math.exp(-(c2 - self.cur) / temp):
                self.S = S2
                self.cur = c2
        if self.cur == 0:
            return self.S.copy()
        return None


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n = 2 * m * k
        e = haar_edges(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    chains = []
    for make in _group_makers(rng):
        if time.monotonic() >= deadline:
            break
        try:
            N, MT, inv, _ = make()
        except Exception:
            continue
        if 2 * N > best_n:
            chains.append(Chain(N, MT, inv, d, rng))

    while chains and time.monotonic() < deadline:
        for ch in chains:
            if time.monotonic() >= deadline:
                break
            if 2 * ch.N <= best_n:
                continue
            S = ch.run(300)
            if S is None:
                continue
            n = 2 * ch.N
            try:
                edges = haar_edges(ch.MT, S, ch.N)
                ok = n > best_n and lib.is_valid(n, edges, d, D)
            except Exception:
                ok = False
            if ok:
                best_n, best_edges = n, edges
            ch.reset()

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
