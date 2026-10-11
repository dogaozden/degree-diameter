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
        return lib.haar_graph(d, range(d))              # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------ group helpers

def _groups(N, rng, per_k=6):
    """Candidate groups of order N: the cyclic group, plus semidirect Z_m x| Z_k (up to per_k twists per k)."""
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
        for r in rs[:per_k]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


# ----------------------------------------- stage 1: two-base Cayley covers

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


def _cayley_stage(d, D, rng, best, deadline):
    """Difference-cover search giving order 2|G|. Returns the best valid graph found (or `best`)."""
    best_n = best[0]
    lo = best_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return best

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _groups(N, rng, 6):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best_N = best_n // 2
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
                    best_n = n
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


# ------------------------------------------- stage 2: four-base bi-Cayley lifts
#
# NEW IDEA. Use four base vertices a0, a1 (side A) and b0, b1 (side B) and a
# group G of order N. Block (i, j) carries a connection set S_ij, with a_i,x ~
# b_j, x*s for s in S_ij. Degrees are d exactly when the block sizes are
# |S_00| = |S_11| = t and |S_01| = |S_10| = d - t (1 <= t <= d-1), so the order
# is 4N and the graph is bipartite with no loops or duplicate edges.
#
# Left multiplication by G is an automorphism, so the graph is vertex-transitive
# within each base class. Diameter <= 3 therefore reduces to checking the four
# representatives (a0, e), (a1, e), (b0, e), (b1, e). The cost is the total
# number of vertices not within distance 3 of these four representatives. It is
# computed with 0/1 reachability matrices, which keeps each evaluation cheap
# enough for simulated annealing over the connection sets.

class _Quad:
    def __init__(self, N, mul, d, t, rng):
        self.N = N
        self.mul = mul
        self.d = d
        self.t = t
        self.rng = rng
        self.M = np.array([[mul(x, y) for y in range(N)] for x in range(N)], dtype=np.int64)
        self.ar = np.arange(N, dtype=np.int64)
        self.S = [[rng.sample(range(N), t if i == j else d - t) for j in range(2)] for i in range(2)]
        self.steps = 0
        self.cost = self._cost()

    def _cost(self):
        N = self.N
        V = 4 * N
        A = np.zeros((V, V), dtype=np.float32)
        ar = self.ar
        for i in range(2):
            for j in range(2):
                a_base = i * N
                b_base = (2 + j) * N
                for s in self.S[i][j]:
                    a = a_base + ar
                    b = b_base + self.M[:, s]
                    A[a, b] = 1.0
                    A[b, a] = 1.0
        idx = np.arange(V)
        A[idx, idx] += 1.0                      # closed neighbourhoods
        R = np.zeros((4, V), dtype=np.float32)
        R[0, 0] = 1.0
        R[1, N] = 1.0
        R[2, 2 * N] = 1.0
        R[3, 3 * N] = 1.0
        for _ in range(3):
            R = ((R @ A) > 0).astype(np.float32)
        return int(4 * V - R.sum())

    def step(self, T):
        rng = self.rng
        i = rng.randrange(2)
        j = rng.randrange(2)
        L = self.S[i][j]
        k = rng.randrange(len(L))
        y = rng.randrange(self.N)
        if y in L:
            return
        old = L[k]
        L[k] = y
        new = self._cost()
        delta = new - self.cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            self.cost = new
        else:
            L[k] = old

    def run(self, steps, T):
        for _ in range(steps):
            if self.cost == 0:
                return True
            self.step(T)
            self.steps += 1
        return self.cost == 0


def _quad_stage(d, D, rng, best, deadline):
    best_n = best[0]
    lo4 = best_n // 4 + 1
    hi4 = lib.moore_bound(d, D) // 4
    if lo4 > hi4:
        return best

    specs = []
    for N in range(lo4, hi4 + 1):
        if N < 2 * d:
            continue
        for _order, mul, _inv in _groups(N, rng, 3):
            for t in rng.sample(range(1, d), min(2, d - 1)):
                specs.append((N, mul, t))

    pending = specs
    pool = []
    K = 4
    chunk = 400
    T = 0.6
    max_steps = 40000
    while time.monotonic() < deadline and (pool or pending):
        while len(pool) < K and pending:
            N, mul, t = pending.pop(0)
            if 4 * N <= best_n:
                continue
            pool.append(_Quad(N, mul, d, t, rng))
        if not pool:
            break
        for st in list(pool):
            if time.monotonic() >= deadline:
                break
            if 4 * st.N <= best_n:
                pool.remove(st)
                continue
            if st.run(chunk, T):
                darts = [(i, 2 + j, s) for i in range(2) for j in range(2) for s in st.S[i][j]]
                n, edges = lib.group_lift(4, darts, st.N, st.mul)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_n = n
                pool.remove(st)
            elif st.steps > max_steps:
                pool.remove(st)
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

    budget = deadline - start
    best = (base_n, base_e)
    best = _cayley_stage(d, D, rng, best, start + 0.2 * budget)
    best = _quad_stage(d, D, rng, best, deadline)

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
