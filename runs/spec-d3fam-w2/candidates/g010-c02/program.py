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
        return lib.haar_graph(d, range(d))              # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ group candidates

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


# ------------------------------------------------ Stage 1: 2-vertex difference covers

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


def _diff_cover_stage(d, D, base_n, base_e, rng, deadline):
    """Search 2-vertex Cayley-type lifts; return (n, edges) or None."""
    lo = base_n // 2 + 1
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
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


# ------------------------------------------------ Stage 2: 3+3 block voltage lifts

def _k_matrix(d, t):
    """t x t dart-count matrix with all row and column sums equal to d."""
    q, r = divmod(d, t)
    return [[q + (1 if (j - i) % t < r else 0) for j in range(t)] for i in range(t)]


class _BlockJob:
    """Annealing over voltages of a t+t base multigraph lifted over a group of order N.

    Base A-vertices 0..t-1, B-vertices t..2t-1. Dart (i, t+j, g) joins A_i to B_j
    with a distinct voltage set per pair, so the lift is d-regular, bipartite,
    and simple. Objective: number of vertex pairs at distance > 3.
    """

    def __init__(self, N, mul, d, t, rng):
        self.N = N
        self.mul = mul
        self.t = t
        self.rng = rng
        self.alive = True
        self.K = _k_matrix(d, t)
        self.V = {(i, j): rng.sample(range(N), self.K[i][j])
                  for i in range(t) for j in range(t)}
        self.keys = list(self.V.keys())
        self.T = 1.0
        self.cur = self._score()

    def _lift(self):
        darts = [(i, self.t + j, g) for (i, j), gs in self.V.items() for g in gs]
        return lib.group_lift(2 * self.t, darts, self.N, self.mul)

    def _score(self):
        n, e = self._lift()
        return lib.bad_pairs(n, e, 3)

    def run(self, until):
        rng = self.rng
        while time.monotonic() < until:
            if self.cur == 0:
                return True
            key = self.keys[rng.randrange(len(self.keys))]
            gs = self.V[key]
            idx = rng.randrange(len(gs))
            g = rng.randrange(self.N)
            if g in gs:
                continue
            old = gs[idx]
            gs[idx] = g
            new = self._score()
            if new <= self.cur or rng.random() < math.exp(-(new - self.cur) / self.T):
                self.cur = new
            else:
                gs[idx] = old
        return self.cur == 0


def _block_stage(d, D, best, rng, deadline, t=3):
    """Search t+t block lifts with order above the current best; return best (n, edges)."""
    moore = lib.moore_bound(d, D)
    hi = moore // (2 * t)
    lo = best[0] // (2 * t) + 1
    if lo > hi:
        return best
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d // t + 2:
            continue
        for _order, mul, _inv in _group_list(N, rng):
            if time.monotonic() >= deadline:
                break
            jobs.append(_BlockJob(N, mul, d, t, rng))
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if not job.alive or 2 * t * job.N <= best[0]:
                job.alive = False
                continue
            slice_end = min(deadline, time.monotonic() + 0.3)
            if job.run(slice_end):
                n, edges = job._lift()
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                job.alive = False
        jobs = [j for j in jobs if j.alive and 2 * t * j.N > best[0]]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)

    # Stage 1: 2-vertex difference-cover lifts (the parent's construction).
    found = _diff_cover_stage(d, D, base_n, base_e, rng, start + 0.35 * total)
    if found is not None and found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
        best = found

    # Stage 2: 3+3 block voltage lifts, aiming above the current best order.
    best = _block_stage(d, D, best, rng, deadline, t=3)

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
