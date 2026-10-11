import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: projective plane incidence (Moore-extremal when d-1 is a prime
# power), the Araujo-Pardo & Lopez record family for d = q+2, and K_{d,d}.
# The largest valid one is the starting point for the search.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _al_candidate(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2, q a prime power >= 3."""
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _base(d, D):
    """Best verified baseline graph for (d, D)."""
    if d < 1 or D < 1:
        return 1, []
    best = (2, [(0, 1)])
    if d >= 2 and D >= 2:
        best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D >= 3 and d >= 3:
        for make in (_pg_candidate, _al_candidate):
            try:
                cand = make(d)
            except Exception:
                cand = None
            if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
    return best


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups G of order N with a difference cover S:
# a_x ~ b_{x s} for s in S, |S| = d, and S S^{-1} = G. This gives diameter 3
# and order 2N with N <= d(d-1)+1. Cyclic groups and semidirect products
# Z_m x| Z_k are both searched. Groups are handled through lib.group_lift.
# ----------------------------------------------------------------------------

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus a sample of semidirect products Z_m x| Z_k."""
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

    cnt[g] counts ordered pairs (a, b) in S x S with a b^{-1} = g, and zeros
    is the number of g with cnt[g] == 0. A single-element swap costs O(d).
    """

    def __init__(self, N, R, d, rng, T):
        self.N = N
        self.R = R
        self.d = d
        self.rng = rng
        self.T = T
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

    def _step(self):
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
        if delta <= 0 or self.rng.random() < math.exp(-delta / self.T):
            S[i] = x
        else:
            self._apply(x, others, -1)
            self._apply(old, others, +1)

    def run(self, steps, deadline):
        """Advance by up to `steps` moves; return True once S is a difference cover."""
        if self.done:
            return True
        for k in range(steps):
            if self.zeros == 0:
                break
            if (k & 127) == 0 and time.monotonic() > deadline:
                return False
            self._step()
        if self.zeros == 0:
            self.done = True
        return self.done


# ---------------------------------------------------------------- driver

def _search(d, base_n, base_e, D, rng, deadline):
    """Round-robin annealing over (N, group) jobs, largest N first. Returns best (n, edges) or None."""
    lo = base_n // 2 + 1          # need 2N > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return None

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None,
                         "dead": False, "T": rng.choice([0.4, 0.6, 0.9])})

    best = None
    best_N = lo - 1
    chunk = 1500
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng, job["T"])
            st = job["st"]
            if st.run(chunk, deadline):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _base(d, D)
    if base_n <= 1 or not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Moore-extremal case (d-1 a prime power, D = 3) is already optimal,
    # and the search only applies to diameter >= 3 with d >= 3.
    if D < 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    try:
        best = _search(d, base_n, base_e, D, rng, deadline)
    except Exception:
        best = None

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
