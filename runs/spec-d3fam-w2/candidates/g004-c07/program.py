import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known constructions (always validated before use):
#   * K_{d,d} (diameter 2), cycles for d = 2, K_2 for D = 1.
#   * Projective plane incidence PG(2, q) for the largest prime power q <= d-1.
#   * Araujo-Pardo & Lopez record for d = q+2 (q a prime power), D = 3.
#
# Search (D = 3): bi-Cayley graph over a group G of order N with a set S of
# size d such that S S^-1 = G. Then a_x ~ b_{x s} (s in S) gives a d-regular
# bipartite graph on 2N vertices with diameter <= 3. Simulated annealing on S
# keeps cnt[g] = #ordered pairs (a, b) in S x S with a b^-1 = g, so one swap
# costs O(d). Groups: cyclic plus sampled semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------


def _known(d, D):
    """Best valid known construction for (d, D), or the safe K_{d,d}/cycle fallback."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    cands = [lib.haar_graph(d, range(d))]          # K_{d,d}, diameter 2
    if D == 3:
        if lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))   # Moore-extremal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
    best = None
    for n, e in cands:
        if (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best if best is not None else (1, [])


def _group_list(N, rng):
    """Cyclic group of order N plus a sample of semidirect products Z_m x| Z_k."""
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
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


class _Search:
    """Resumable annealing for d distinct S with S S^-1 = G (incremental coverage counts)."""

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
        """Advance up to `steps` moves; True once S is a difference cover."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []

    best = _known(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    # Only the diameter-3 regime is searched. d = 3 and d-1 a prime power
    # give Moore-extremal graphs, which cannot be beaten.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return best

    lo = best[0] // 2 + 1            # a new group order N gives order 2N > best
    hi = d * (d - 1) + 1             # hard bound for diameter-3 difference covers
    if lo > hi:
        return best

    STEP_LIMIT = 300000              # restart a job's annealing after this many moves
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv,
                         "st": None, "dead": False, "steps": 0})

    best_N = lo - 1
    chunk = 1500
    T = 0.6

    try:
        while jobs and time.monotonic() < deadline:
            for job in list(jobs):
                if time.monotonic() >= deadline:
                    break
                if job["N"] <= best_N or job["dead"]:
                    continue
                if job["st"] is None or job["steps"] > STEP_LIMIT:
                    R = _ratio_table(job["N"], job["mul"], job["inv"])
                    job["st"] = _Search(job["N"], R, d, rng)
                    job["steps"] = 0
                st = job["st"]
                job["steps"] += chunk
                if st.run(chunk, deadline, T):
                    n, edges = lib.group_lift(
                        2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                    if n > best[0] and lib.is_valid(n, edges, d, D):
                        best = (n, edges)
                        best_N = job["N"]
                        break
                    job["dead"] = True
            jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    except Exception:
        pass

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return _known(d, D)
