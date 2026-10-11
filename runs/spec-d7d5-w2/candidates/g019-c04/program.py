"""Random-start bipartite local search with grow-and-repair (bold rewrite).

Approach for D >= 3 (other than exact projective-plane cases):
- Represent a d-regular bipartite graph on h + h vertices as d perfect matchings
  (layers) P[l]: A-index i -> B-index P[l][i].
- Start from a circulant (Haar) layout and repair it by simulated annealing.
  Moves swap two targets inside one layer, which keeps every degree at exactly d
  and keeps the graph simple (checked with a multiplicity matrix M).
- The cost is the number of ordered vertex pairs at distance > D, computed with
  packed uint64 bitsets (numpy). A cost of 0 means the diameter is at most D.
- Growth: a "vertex split" inserts one A-vertex and one B-vertex in every layer,
  keeping regularity and the bipartition. Annealing then repairs the new defects.
- Every size that anneals to cost 0 is snapshotted. The final snapshot is
  verified with lib.is_valid. Fallbacks are the projective plane (when exact)
  and K_{d,d}, so the output is always valid.
"""
import math
import random
import time

import numpy as np

import lib


_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(min(d - 1, 25), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _deficits(nbr, N, D):
    """Per-vertex count of vertices NOT within distance D, using packed bitsets."""
    W = (N + 63) // 64
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for row in nbr:
            new |= reach[row]
        reach = new
    cnt = _POP8[reach.view(np.uint8)].sum(axis=1)
    return N - cnt


class _Bip:
    """d-regular bipartite graph stored as d perfect matchings between h A-vertices and h B-vertices."""

    def __init__(self, d, h, shifts=None, P=None):
        self.d = d
        self.h = h
        if P is None:
            ar = np.arange(h, dtype=np.int64)
            P = np.array([(ar + s) % h for s in shifts], dtype=np.int64)
        self.P = P
        self._rebuild()

    def _rebuild(self):
        d, h = self.d, self.h
        ar = np.arange(h, dtype=np.int64)
        self.Q = np.empty((d, h), dtype=np.int64)
        self.M = np.zeros((h, h), dtype=np.int32)
        self.nbr = np.empty((d, 2 * h), dtype=np.int64)
        for l in range(d):
            self.Q[l, self.P[l]] = ar
            self.M[ar, self.P[l]] += 1
            self.nbr[l, :h] = h + self.P[l]
            self.nbr[l, h:] = self.Q[l]

    def legal(self, l, i, j):
        """Swapping the targets of A-vertices i and j in layer l must not create a duplicate edge."""
        P = self.P[l]
        return self.M[i, P[j]] == 0 and self.M[j, P[i]] == 0

    def swap(self, l, i, j):
        """Swap the B-targets of A-vertices i and j in layer l (an involution, so it is also the undo)."""
        h = self.h
        P = self.P[l]
        pi, pj = int(P[i]), int(P[j])
        M = self.M
        M[i, pi] -= 1
        M[j, pj] -= 1
        M[i, pj] += 1
        M[j, pi] += 1
        P[i], P[j] = pj, pi
        self.Q[l, pj] = i
        self.Q[l, pi] = j
        self.nbr[l, i] = h + pj
        self.nbr[l, j] = h + pi
        self.nbr[l, h + pj] = i
        self.nbr[l, h + pi] = j

    def grow(self, rng):
        """Vertex split: add one A-vertex and one B-vertex, keeping d-regularity and simplicity."""
        d, h = self.d, self.h
        usedA, usedB = set(), set()
        picks = []
        for l in range(d):
            order = list(range(h))
            rng.shuffle(order)
            pick = -1
            for i in order:
                if i not in usedA and int(self.P[l, i]) not in usedB:
                    pick = i
                    break
            if pick < 0:
                return False
            usedA.add(pick)
            usedB.add(int(self.P[l, pick]))
            picks.append(pick)
        P2 = np.empty((d, h + 1), dtype=np.int64)
        for l in range(d):
            i = picks[l]
            old = int(self.P[l, i])
            P2[l, :h] = self.P[l]
            P2[l, i] = h
            P2[l, h] = old
        self.h = h + 1
        self.P = P2
        self._rebuild()
        return True

    def edges(self):
        h = self.h
        out = []
        for l in range(self.d):
            P = self.P[l]
            out.extend((i, h + int(P[i])) for i in range(h))
        return out


def _anneal(st, D, rng, deadline):
    """Simulated annealing on the number of unreached pairs. Returns True when the cost reaches 0."""
    d = st.d
    N = 2 * st.h
    deff = _deficits(st.nbr, N, D)
    cost = int(deff.sum())
    if cost == 0:
        return True
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = max(0.2, 2.0 * (1.0 - frac))
        l = rng.randrange(d)
        if rng.random() < 0.5:
            bad = np.flatnonzero(deff)
            u = int(bad[rng.randrange(bad.size)])
            i = u if u < st.h else int(st.Q[l, u - st.h])
        else:
            i = rng.randrange(st.h)
        j = rng.randrange(st.h)
        if i == j or not st.legal(l, i, j):
            continue
        st.swap(l, i, j)
        d2 = _deficits(st.nbr, N, D)
        c2 = int(d2.sum())
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, deff = c2, d2
        else:
            st.swap(l, i, j)
    return cost == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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
            best, best_n = (n, e), n

    # Exact projective-plane construction for diameter 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    rng = random.Random(seed)
    h0 = max(d + 1, 150)
    st = _Bip(d, h0, rng.sample(range(h0), d))
    good = None

    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, 0.5 * remaining))
        if not _anneal(st, D, rng, slice_end):
            break
        good = (st.h, st.P.copy())
        if not st.grow(rng):
            break

    if good is not None:
        h, P = good
        st2 = _Bip(d, h, None, P=P.copy())
        consider(2 * h, st2.edges())

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
