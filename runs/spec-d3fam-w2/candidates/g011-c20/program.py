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


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Distances are at most 3 when
#   S S^{-1} = G   (same-side distance 2 on A)  and
#   S^{-1} S = G   (same-side distance 2 on B),
# and cross-side pairs are then covered automatically. So the task is a pair of
# difference-cover conditions for a set S of d distinct group elements.
# Order 2|G| with |G| <= d(d-1)+1.

def _direct(m, k):
    """Abelian group Z_m x Z_k, element (a, b) coded as a*k+b."""
    def mul(x, y):
        a, b = divmod(x, k)
        c, e = divmod(y, k)
        return ((a + c) % m) * k + (b + e) % k

    def inv(x):
        a, b = divmod(x, k)
        return ((-a) % m) * k + (-b) % k

    return mul, inv


def _group_list(N, rng, cap):
    """Candidate groups of order N: cyclic first, then a sample of other groups."""
    groups = [lib.cyclic_group(N)[1:]]
    extra = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k <= m and math.gcd(m, k) > 1:
            extra.append(_direct(m, k))
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                _, mul, inv = lib.semidirect_group(m, k, r)
                extra.append((mul, inv))
            except ValueError:
                pass
    rng.shuffle(extra)
    return (groups + extra)[:cap]


class _Search:
    """Resumable annealing for d distinct elements S with S S^{-1} = G and S^{-1} S = G.

    cnt1[g] counts ordered pairs (a, b) in S x S with a b^{-1} = g,
    cnt2[g] counts ordered pairs with a^{-1} b = g. zeros is the number of
    uncovered entries over both tables; the search stops when zeros == 0.
    """

    STALL = 120000

    def __init__(self, N, mul, inv, d, rng):
        self.N = N
        self.d = d
        self.rng = rng
        il = [inv(x) for x in range(N)]
        self.R1 = [[mul(x, il[y]) for y in range(N)] for x in range(N)]
        self.R2 = [[mul(il[x], y) for y in range(N)] for x in range(N)]
        self.reset()

    def reset(self):
        N, d = self.N, self.d
        self.S = self.rng.sample(range(N), d)
        self.c1 = [0] * N
        self.c2 = [0] * N
        for a in self.S:
            for b in self.S:
                self.c1[self.R1[a][b]] += 1
                self.c2[self.R2[a][b]] += 1
        self.zeros = self.c1.count(0) + self.c2.count(0)
        self.best = self.zeros
        self.stall = 0

    @staticmethod
    def _upd(cnt, R, e, others, sign):
        """Add (sign>0) or remove (sign<0) all ordered pairs involving e; return change in zeros."""
        Re = R[e]
        gs = [Re[e]]
        gs.extend(Re[o] for o in others)
        gs.extend(R[o][e] for o in others)
        ch = 0
        if sign > 0:
            for g in gs:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
        else:
            for g in gs:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
        return ch

    def _move(self, T):
        S = self.S
        i = self.rng.randrange(self.d)
        x = self.rng.randrange(self.N)
        if x in S:
            return
        old = S[i]
        others = S[:i] + S[i + 1:]
        R1, R2, c1, c2 = self.R1, self.R2, self.c1, self.c2
        delta = self._upd(c1, R1, old, others, -1) + self._upd(c2, R2, old, others, -1)
        delta += self._upd(c1, R1, x, others, 1) + self._upd(c2, R2, x, others, 1)
        if delta <= 0 or self.rng.random() < math.exp(-delta / T):
            S[i] = x
            self.zeros += delta
        else:
            self._upd(c1, R1, x, others, -1)
            self._upd(c2, R2, x, others, -1)
            self._upd(c1, R1, old, others, 1)
            self._upd(c2, R2, old, others, 1)

    def run(self, steps, deadline, T):
        """Advance by up to `steps` moves; return True once S is a double difference cover."""
        if self.zeros == 0:
            return True
        for k in range(steps):
            if self.zeros == 0:
                break
            if (k & 255) == 0 and time.monotonic() > deadline:
                break
            self._move(T)
            if self.zeros < self.best:
                self.best = self.zeros
                self.stall = 0
            else:
                self.stall += 1
                if self.stall > self.STALL:
                    self.reset()
        return self.zeros == 0


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    # Each job: dict with N, mul, inv, state (built lazily), dead flag.
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for mul, inv in _group_list(N, rng, cap=8):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
    best_N = lo - 1
    chunk = 3000
    T = 0.6

    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                job["st"] = _Search(job["N"], job["mul"], job["inv"], d, rng)
            st = job["st"]
            if st.run(chunk, deadline, T):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
