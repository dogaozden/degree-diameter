"""Covering-family construction for diameter 3.

Base: incidence graph of PG(2, q), q the largest prime power <= d-1, so each
vertex has spare degree s = d - q - 1. Add k "A" vertices and k "B" vertices.
A_i joins a set F_i of lines and B_i joins the same index set F_i of points.

If F_i covers every point (each point lies on a line of F_i), F_i and F_t share
an index (A_i, A_t at distance 2), and every index is used by at most s families,
then the result has diameter 3 and max degree d. Order = 2(q^2+q+1) + 2k.
The pencil families from a conic reproduce the 394 record for d=16. A simulated
annealing search over families adds one family at a time, aiming for k = 15, which
gives order 396 and beats the record. Every output is verified with lib.is_valid,
and the fallback is always a valid graph.
"""
import math
import random
import time

import lib


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


class _Base:
    """PG(2,q) incidence data. Points are indices 0..m-1 and lines are m..2m-1."""

    def __init__(self, q):
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        self.q = q
        self.m = m
        self.edges = [(int(u), int(v)) for u, v in edges]
        # Q[j]: points on line j. LP[x]: lines through point x. Incidence is symmetric
        # in the shared index set, so the same index families serve both sides.
        self.Q = [[] for _ in range(m)]
        self.LP = [[] for _ in range(m)]
        for x, v in self.edges:
            j = v - m
            self.Q[j].append(x)
            self.LP[x].append(j)


class _Families:
    """A set of index-families with incremental cover / intersection / load bookkeeping.

    U = total uncovered (family, index) pairs. N = number of family pairs with empty intersection.
    cost = U + W * N.
    """

    def __init__(self, base, s, W=2):
        self.base = base
        self.m = base.m
        self.s = s
        self.W = W
        self.fams = []
        self.mem = []
        self.cov = []
        self.inter = []
        self.load = [0] * self.m
        self.U = 0
        self.N = 0

    def cost(self):
        return self.U + self.W * self.N

    def add(self, F):
        m = self.m
        Q = self.base.Q
        i = len(self.fams)
        mem = bytearray(m)
        cov = [0] * m
        for j in F:
            mem[j] = 1
            self.load[j] += 1
            for x in Q[j]:
                cov[x] += 1
        self.U += sum(1 for c in cov if c == 0)
        row = []
        for t in range(i):
            Mt = self.mem[t]
            c = 0
            for j in F:
                c += Mt[j]
            row.append(c)
            self.inter[t].append(c)
            if c == 0:
                self.N += 1
        row.append(0)
        self.inter.append(row)
        self.fams.append(list(F))
        self.mem.append(mem)
        self.cov.append(cov)
        return i

    def move(self, i, pos, jin):
        """Replace the line at position pos of family i with jin. Returns (jout, dU, dN)."""
        Q = self.base.Q
        F = self.fams[i]
        jout = F[pos]
        cov_i = self.cov[i]
        dU = 0
        for x in Q[jout]:
            cov_i[x] -= 1
            if cov_i[x] == 0:
                dU += 1
        for x in Q[jin]:
            if cov_i[x] == 0:
                dU -= 1
            cov_i[x] += 1
        dN = 0
        inter_i = self.inter[i]
        for t in range(len(self.fams)):
            if t == i:
                continue
            delta = self.mem[t][jin] - self.mem[t][jout]
            if delta:
                old = inter_i[t]
                new = old + delta
                if old == 0 and new > 0:
                    dN -= 1
                elif old > 0 and new == 0:
                    dN += 1
                inter_i[t] = new
                self.inter[t][i] = new
        mem_i = self.mem[i]
        mem_i[jout] = 0
        mem_i[jin] = 1
        self.load[jout] -= 1
        self.load[jin] += 1
        F[pos] = jin
        self.U += dU
        self.N += dN
        return jout, dU, dN


def _random_family(st, r, rng):
    cand = [j for j in range(st.m) if st.load[j] < st.s]
    if len(cand) < r:
        return None
    return rng.sample(cand, r)


def _anneal(st, rng, deadline, T0, T1):
    """Anneal until cost 0 (returns True) or the deadline (returns False)."""
    k = len(st.fams)
    m = st.m
    LP = st.base.LP
    s = st.s
    W = st.W
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T = T0
    it = 0
    while st.cost() > 0:
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                return False
            frac = min(1.0, (now - t_start) / span)
            T = T0 * (T1 / T0) ** frac
        it += 1
        i = rng.randrange(k)
        F = st.fams[i]
        pos = rng.randrange(len(F))
        if rng.random() < 0.6:
            # Targeted proposal: cover a random uncovered index with a line through it.
            cov_i = st.cov[i]
            x = -1
            for _ in range(20):
                c = rng.randrange(m)
                if cov_i[c] == 0:
                    x = c
                    break
            if x < 0:
                continue
            jin = LP[x][rng.randrange(len(LP[x]))]
        else:
            jin = rng.randrange(m)
        if st.mem[i][jin] or st.load[jin] >= s:
            continue
        jout, dU, dN = st.move(i, pos, jin)
        d = dU + W * dN
        if d <= 0 or rng.random() < math.exp(-d / T):
            continue
        st.move(i, pos, jout)  # reject: revert
    return True


def _conic_pencils(base, q, s):
    """Pencils at the points of a conic (plus nucleus for even q), if loads allow."""
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    load = [0] * base.m
    for x in S:
        for j in base.LP[x]:
            load[j] += 1
    if max(load) > s:
        return []
    return [list(base.LP[x]) for x in S]


def _graph(base, fams):
    """Assemble the graph: points 0..m-1, lines m..2m-1, A-vertices, B-vertices."""
    m = base.m
    k = len(fams)
    n = 2 * m + 2 * k
    E = list(base.edges)
    for i, F in enumerate(fams):
        a = 2 * m + i
        for j in F:
            E.append((a, m + j))
        b = 2 * m + k + i
        for x in F:
            E.append((x, b))
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D >= 3:
        q = _largest_prime_power_at_most(d - 1)
        if q is not None:
            s = d - q - 1
            base = _Base(q)
            consider(2 * base.m, base.edges)  # plain PG(2,q) incidence graph
            if s >= 1:
                good = _conic_pencils(base, q, s)
                if good:
                    consider(*_graph(base, good))
                # Grow the family set one family at a time with annealing.
                while time.monotonic() < deadline:
                    now = time.monotonic()
                    rem = deadline - now
                    slice_end = now + max(3.0, 0.5 * rem)
                    st = _Families(base, s)
                    for F in good:
                        st.add(F)
                    F_new = _random_family(st, d, rng)
                    if F_new is None:
                        break
                    st.add(F_new)
                    if _anneal(st, rng, min(slice_end, deadline), 1.0, 0.05):
                        good = [list(F) for F in st.fams]
                        consider(*_graph(base, good))

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, [(int(u), int(v)) for u, v in best_E]
