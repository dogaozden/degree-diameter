import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: record Araujo-Pardo/Lopez graph, projective plane incidence,
# K_{d,d}, and the even cycle for d = 2.
# ----------------------------------------------------------------------------

def _baseline(d, D):
    """Best verified-by-construction graph among the known families; always valid."""
    cands = []
    if d == 2:
        n = 2 * D
        cands.append((n, [(i, (i + 1) % n) for i in range(n)]))
    if D == 2 or D >= 2:
        cands.append(lib.haar_graph(d, range(d)))          # K_{d,d}, diameter 2
    if D == 3:
        if lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))  # Moore-extremal
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))  # record family
            except Exception:
                pass
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
    best = None
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    if best is None:
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over groups G of order N.
#
# Base: two vertices a, b with darts (a, b, s) for s in S, |S| = d, so
# a_x ~ b_{x s}. Every vertex has degree d, no loops, no duplicate edges.
# If S S^{-1} = G then the diameter is at most 3, giving order 2N with
# N <= d(d-1)+1 (a "difference cover" of size d).
#
# Search: resumable simulated annealing per (group, N) job, round-robin over
# many groups (cyclic and semidirect Z_m x| Z_k), largest N first.
# ----------------------------------------------------------------------------

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus a random sample of semidirect Z_m x| Z_k."""
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
    """Resumable annealing for d distinct elements S with S S^{-1} = G.

    cnt[g] = number of ordered pairs (a, b) in S x S with a b^{-1} = g;
    zeros = number of g with cnt[g] == 0. A single-element swap costs O(d).
    """

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
        """Add (sign=+1) or remove (sign=-1) the ordered pairs of x with itself and with others."""
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
        """Advance by up to `steps` moves; return True once S is a difference cover."""
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


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    base_n, base_e = _baseline(d, D)

    # Moore-extremal regime (projective plane incidence) is optimal: no search.
    if D == 3 and lib.is_prime_power(d - 1):
        return base_n, base_e
    if D < 3 or d < 3:
        return base_n, base_e

    try:
        lo = base_n // 2 + 1          # need 2N > current best order
        hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
        if lo <= hi:
            jobs = []                 # one job per (N, group), largest N first
            for N in range(hi, lo - 1, -1):
                if N < d:
                    continue
                for _order, mul, inv in _group_list(N, rng):
                    jobs.append({"N": N, "mul": mul, "inv": inv,
                                 "st": None, "dead": False})

            best = None
            best_N = lo - 1
            chunk = 1500              # moves per job per round-robin visit
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
                        n, edges = lib.group_lift(
                            2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                        if n > base_n and lib.is_valid(n, edges, d, D):
                            best = (n, edges)
                            best_N = job["N"]
                            break
                        job["dead"] = True
                jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

            if best is not None and lib.is_valid(best[0], best[1], d, D):
                return best
    except Exception:
        pass

    if lib.is_valid(base_n, base_e, d, D):
        return base_n, base_e
    return lib.haar_graph(d, range(d))
