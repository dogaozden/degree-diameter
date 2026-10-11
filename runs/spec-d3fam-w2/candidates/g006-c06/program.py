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


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 exactly when
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# which gives order 2|G| with |G| <= d(d-1)+1.
#
# Normalisation: replacing S by S*s0^{-1} keeps S S^{-1} unchanged, so we may
# assume the identity (code 0 in both cyclic and semidirect encodings) is in S.

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


class _Search:
    """Resumable annealing for d distinct elements S (containing the identity)
    with S S^{-1} = G.

    cnt[g] = number of ordered pairs (a, b) in S x S with a b^{-1} = g, and
    zeros = number of g with cnt[g] == 0. Ratios are computed on the fly from
    the group operation, so no N x N table is built (cheap to start many jobs).
    Stalled runs are restarted from a fresh random set.
    """

    PATIENCE = 30000

    def __init__(self, N, mul, inv, d, rng):
        self.N = N
        self.d = d
        self.rng = rng
        self.mul = mul
        self.iv = [inv(y) for y in range(N)]
        self._reset()

    def ratio(self, x, y):
        """x * y^{-1}."""
        return self.mul(x, self.iv[y])

    def _reset(self):
        self.S = [0] + self.rng.sample(range(1, self.N), self.d - 1)
        self.cnt = [0] * self.N
        for a in self.S:
            for b in self.S:
                self.cnt[self.ratio(a, b)] += 1
        self.zeros = sum(1 for c in self.cnt if c == 0)
        self.done = self.zeros == 0
        self.best_zeros = self.zeros
        self.since = 0

    def _apply(self, x, others, sign):
        """Add (sign=+1) or remove (sign=-1) the ordered pairs of x with itself and with others."""
        cnt = self.cnt
        gs = [self.ratio(x, x)]
        gs += [self.ratio(x, b) for b in others]
        gs += [self.ratio(b, x) for b in others]
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
        i = self.rng.randrange(1, self.d)      # never replace the identity
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
            if self.zeros < self.best_zeros:
                self.best_zeros = self.zeros
                self.since = 0
            else:
                self.since += 1
                if self.since > self.PATIENCE:
                    self._reset()
                    if self.done:
                        break
        if self.zeros == 0:
            self.done = True
        return self.done


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    jobs = []                     # dicts: N, mul, inv, T, st, dead
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv,
                         "T": rng.choice([0.3, 0.5, 0.8]),
                         "st": None, "dead": False})

    best = None                   # (n, edges)
    best_N = lo - 1
    chunk = 1500                  # moves per job per round-robin visit

    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                job["st"] = _Search(job["N"], job["mul"], job["inv"], d, rng)
            st = job["st"]
            if st.run(chunk, deadline, job["T"]):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S],
                                          job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    if best is not None:
        return best
    return base_n, base_e
