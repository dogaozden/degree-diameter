import math
import random
import time

import numpy as np

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


# ------------------------------------------------ group-lift helpers
#
# Any lift over a group G is invariant under left multiplication by G, so the
# distance profile from (u, x) depends only on the base vertex u. This lets us
# test the diameter by a few ball computations instead of all-pairs.


def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus some semidirect Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:6]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


class _Search:
    """Resumable annealing for d distinct elements S with S S^{-1} = G."""

    def __init__(self, N, R, d, rng):
        self.N = N
        self.R = R
        self.d = d
        self.rng = rng
        self.S = rng.sample(range(N), d)
        self.cnt = [0] * N
        for a in self.S:
            for b in self.S:
                self.cnt[R[a][b]] += 1
        self.zeros = sum(1 for c in self.cnt if c == 0)
        self.done = self.zeros == 0

    def _apply(self, x, others, sign):
        cnt, R = self.cnt, self.R
        Rx = R[x]
        gs = [Rx[x]] + [Rx[b] for b in others] + [R[b][x] for b in others]
        if sign < 0:
            for g in gs:
                cnt[g] -= 1
                if cnt[g] == 0:
                    self.zeros += 1
        else:
            for g in gs:
                if cnt[g] == 0:
                    self.zeros -= 1
                cnt[g] += 1

    def _step(self, T):
        S = self.S
        i = self.rng.randrange(self.d)
        x = self.rng.randrange(self.N)
        if x in S:
            return
        old = S[i]
        others = S[:i] + S[i + 1:]
        before = self.zeros
        self._apply(old, others, -1)
        self._apply(x, others, +1)
        delta = self.zeros - before
        if delta <= 0 or self.rng.random() < math.exp(-delta / T):
            S[i] = x
        else:
            self._apply(x, others, -1)
            self._apply(old, others, +1)

    def run(self, steps, deadline, T):
        if self.done:
            return True
        for k in range(steps):
            if self.zeros == 0:
                break
            if (k & 127) == 0 and time.monotonic() > deadline:
                return False
            self._step(T)
        if self.zeros == 0:
            self.done = True
        return self.done


class _OrbitJob:
    """Annealing over voltages of a 4-vertex bipartite base multigraph.

    Base: A-vertices 0, 1 and B-vertices 2, 3 with multiplicities
    [[k, d-k], [d-k, k]], so every base vertex has d darts. Cost is the number
    of (base source, vertex) pairs at distance more than 3, computed with
    numpy ball expansion from the four fibre identities.
    """

    def __init__(self, N, mul, TT, d, k, rng):
        self.N = N
        self.mul = mul
        self.TT = TT
        self.rng = rng
        self.pairs = ([(0, 2)] * k + [(0, 3)] * (d - k)
                      + [(1, 2)] * (d - k) + [(1, 3)] * k)
        self.xs = np.arange(N, dtype=np.int64)
        self.src = np.array([0, N, 2 * N, 3 * N], dtype=np.int64)
        self.dead = False
        self._reset()

    def _cost(self, V):
        N = self.N
        n = 4 * N
        A = np.zeros((n, n), dtype=np.float32)
        for (u, v), g in zip(self.pairs, V):
            a = u * N + self.xs
            b = v * N + self.TT[:, g]
            A[a, b] = 1.0
            A[b, a] = 1.0
        S = np.zeros((4, n), dtype=bool)
        S[np.arange(4), self.src] = True
        for _ in range(3):
            S = S | ((S.astype(np.float32) @ A) > 0.0)
        return 4 * n - int(S.sum())

    def _reset(self):
        self.V = [self.rng.randrange(self.N) for _ in self.pairs]
        self.cur = self._cost(self.V)
        self.T = self.rng.uniform(0.2, 2.0)
        self.stall = 0

    def run(self, moves):
        """Advance up to `moves` steps; return True once the voltages give diameter <= 3."""
        if self.cur == 0:
            return True
        V = self.V
        N = self.N
        rng = self.rng
        for _ in range(moves):
            i = rng.randrange(len(V))
            g = rng.randrange(N)
            if g == V[i]:
                continue
            old = V[i]
            V[i] = g
            c = self._cost(V)
            if c <= self.cur or rng.random() < math.exp(-(c - self.cur) / self.T):
                self.stall = 0 if c < self.cur else self.stall + 1
                self.cur = c
                if c == 0:
                    return True
            else:
                V[i] = old
                self.stall += 1
            if self.stall > 2000:
                self._reset()
                return False
        return False


# ---------------------------------------------------------------- phases

def _cayley_phase(d, D, best_n, rng, deadline):
    """Difference-cover search over 2-vertex Cayley-type lifts. Returns (n, edges) or None."""
    lo = best_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
    best_N = lo - 1
    chunk = 1500
    T = 0.6
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline, T):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


def _orbit_phase(d, D, best_n, rng, deadline):
    """Search 4-vertex base voltage lifts of order 4N > best_n. Returns (n, edges) or None."""
    moore = lib.moore_bound(d, D)
    lo = best_n // 4 + 1
    hi = moore // 4
    if lo > hi or d < 2:
        return None

    jobs = []
    ks_all = list(range(1, d // 2 + 1))
    for N in range(lo, hi + 1):
        for _order, mul, _inv in _group_list(N, rng)[:3]:
            TT = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
            ks = ks_all[:]
            rng.shuffle(ks)
            for k in ks[:2]:
                jobs.append(_OrbitJob(N, mul, TT, d, k, rng))

    best = None
    cur_n = best_n
    while jobs and time.monotonic() < deadline:
        for job in jobs:
            if time.monotonic() >= deadline:
                break
            if 4 * job.N <= cur_n or job.dead:
                continue
            if job.run(300):
                n, edges = lib.group_lift(
                    4, [(u, v, g) for (u, v), g in zip(job.pairs, job.V)], job.N, job.mul)
                if n > cur_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    cur_n = n
                    break
                job.dead = True
        jobs = [j for j in jobs if 4 * j.N > cur_n and not j.dead]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    span = deadline - start

    cay = _cayley_phase(d, D, best[0], rng, start + 0.4 * span)
    if cay is not None:
        best = cay

    orb = _orbit_phase(d, D, best[0], rng, deadline)
    if orb is not None:
        best = orb

    return best
