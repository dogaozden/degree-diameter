import math
import random
import time

import lib


def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)    # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------
# Different construction: multi-fibre cyclic covers of a random
# d-regular bipartite base multigraph on p + p vertices.
#
# Base: union of d perfect matchings between A = {0..p-1} and B = {0..p-1}
# (so every base vertex has degree d; parallel darts are allowed).
# Each dart (i, j, s) with voltage s in Z_N gives the lift edges
#     a_{i,g} ~ b_{j,(g+s) mod N}   for all g.
# Order = 2*p*N. The lift is vertex-transitive within each fibre, so
# diameter <= 3 holds iff every fibre-0 vertex reaches everything within 3
# steps. Reachability is computed with N-bit integer masks and rotations,
# which makes each cost evaluation very cheap.
#
# Searched by simulated annealing on the voltages, minimising the number of
# unreached (fibre, residue) pairs plus a penalty for parallel darts.
# ------------------------------------------------------------------

def _rot(m, s, N, full):
    """Shift the N-bit mask m so that bit g moves to bit (g + s) mod N."""
    if s == 0:
        return m
    return ((m << s) | (m >> (N - s))) & full


def _popcount(x):
    return bin(x).count("1")


class _Cover:
    """Resumable annealing over the voltages of one (p, N) configuration."""

    def __init__(self, p, N, d, rng):
        self.p = p
        self.N = N
        self.d = d
        self.rng = rng
        self.full = (1 << N) - 1
        self.di = []
        self.dj = []
        for k in range(d):
            perm = list(range(p)) if k == 0 else rng.sample(range(p), p)
            for i in range(p):
                self.di.append(i)
                self.dj.append(perm[i])
        self.s = [rng.randrange(N) for _ in self.di]
        self.steps = 0
        self.cost = self._cost(self.s)
        self.done = self.cost == 0

    def _ab(self, A, s):
        """Push A-fibre masks across all darts to B-fibre masks."""
        N, full = self.N, self.full
        out = [0] * self.p
        for t in range(len(self.di)):
            m = A[self.di[t]]
            if m:
                out[self.dj[t]] |= _rot(m, s[t], N, full)
        return out

    def _ba(self, B, s):
        """Push B-fibre masks across all darts to A-fibre masks."""
        N, full = self.N, self.full
        out = [0] * self.p
        for t in range(len(self.di)):
            m = B[self.dj[t]]
            if m:
                out[self.di[t]] |= _rot(m, (N - s[t]) % N, N, full)
        return out

    def _miss(self, side, idx, s):
        """Number of (fibre, residue) pairs NOT within distance 3 of the source vertex."""
        p, N = self.p, self.N
        if side == 0:
            A = [0] * p
            A[idx] = 1
            B1 = self._ab(A, s)
            A2 = self._ba(B1, s)
            B3 = self._ab(A2, s)
            RA = [x | y for x, y in zip(A, A2)]
            RB = [x | y for x, y in zip(B1, B3)]
        else:
            B = [0] * p
            B[idx] = 1
            A1 = self._ba(B, s)
            B2 = self._ab(A1, s)
            A3 = self._ba(B2, s)
            RB = [x | y for x, y in zip(B, B2)]
            RA = [x | y for x, y in zip(A1, A3)]
        miss = 0
        for x in RA:
            miss += N - _popcount(x)
        for x in RB:
            miss += N - _popcount(x)
        return miss

    def _cost(self, s):
        dup = 0
        T = len(s)
        for a in range(T):
            for b in range(a + 1, T):
                if self.di[a] == self.di[b] and self.dj[a] == self.dj[b] and s[a] == s[b]:
                    dup += 1
        total = 4 * dup
        for idx in range(self.p):
            total += self._miss(0, idx, s)
            total += self._miss(1, idx, s)
        return total

    def step(self):
        rng = self.rng
        s = self.s
        T_ = 0.25 + 1.0 * math.exp(-(self.steps % 20000) / 3000.0)
        self.steps += 1
        t = rng.randrange(len(s))
        old = s[t]
        new = rng.randrange(self.N)
        if new == old:
            return
        s[t] = new
        c = self._cost(s)
        delta = c - self.cost
        if delta <= 0 or rng.random() < math.exp(-delta / T_):
            self.cost = c
            if c == 0:
                self.done = True
        else:
            s[t] = old

    def edges(self):
        p, N = self.p, self.N
        off = p * N
        out = []
        for t in range(len(self.di)):
            i, j, sv = self.di[t], self.dj[t], self.s[t]
            for g in range(N):
                out.append((i * N + g, off + j * N + (g + sv) % N))
        return 2 * p * N, out


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    hi_half = d * d - d + 1       # order <= 2 * hi_half for diameter 3
    configs = []
    for p in range(1, min(d, 8) + 1):
        Nmax = hi_half // p
        lo = max(d, base_n // (2 * p) + 1)
        for N in range(lo, min(Nmax, lo + 5) + 1):
            order = 2 * p * N
            if base_n < order <= 2 * hi_half:
                configs.append((order, p, N))
    if not configs:
        return base_n, base_e
    configs.sort()

    states = [{"order": o, "p": p, "N": N, "st": None, "done": False}
              for o, p, N in configs]

    best = None
    best_order = base_n
    CHUNK = 300

    while time.monotonic() < deadline:
        active = [c for c in states if not c["done"] and c["order"] > best_order]
        if not active:
            break
        for c in active:
            if time.monotonic() >= deadline:
                break
            if c["done"] or c["order"] <= best_order:
                continue
            if c["st"] is None:
                c["st"] = _Cover(c["p"], c["N"], d, rng)
            st = c["st"]
            if st.done:
                c["done"] = True
            else:
                for _ in range(CHUNK):
                    st.step()
                    if st.done:
                        break
            if st.done:
                n, edges = st.edges()
                if n > best_order and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_order = n
                c["done"] = True

    if best is not None:
        return best
    return base_n, base_e
