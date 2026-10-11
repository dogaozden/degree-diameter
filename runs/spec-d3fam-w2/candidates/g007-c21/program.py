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
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 when
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# which gives order 2|G| with |G| <= d(d-1)+1.
#
# New in this version:
#   * Non-cyclic abelian groups Z_m x Z_k (r = 1) are always tried, not
#     sampled away. Many good covers live there.
#   * The search is tabu search over best-of-sampled swap moves (instead of
#     blind annealing), with restarts after long stagnation.


def _group_list(N, rng):
    """Candidate groups of order N: cyclic, Z_m x Z_k (always), and some semidirect products."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        try:
            groups.append(lib.semidirect_group(m, k, 1))  # direct product Z_m x Z_k
        except ValueError:
            pass
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


class _Tabu:
    """Tabu search for d distinct elements S with S S^{-1} = G.

    cnt[g] = number of ordered pairs (a, b) in S x S with a b^{-1} = g,
    zeros = number of g with cnt[g] == 0. Each step samples a batch of
    candidate swaps, evaluates each exactly in O(d), and takes the best
    non-tabu one (aspiration allows tabu moves that beat the best seen).
    """

    K = 24          # candidate swaps sampled per step
    TENURE = 7      # steps an removed element stays forbidden
    STALL = 2500    # steps without improvement before a restart

    def __init__(self, N, R, d, rng):
        self.N = N
        self.R = R
        self.d = d
        self.rng = rng
        self.it = 0
        self.tabu_until = [0] * N
        self._restart()

    def _restart(self):
        self.S = self.rng.sample(range(self.N), self.d)
        self.cnt = [0] * self.N
        for a in self.S:
            for b in self.S:
                self.cnt[self.R[a][b]] += 1
        self.zeros = sum(1 for c in self.cnt if c == 0)
        self.best_zeros = self.zeros
        self.last_improve = self.it
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

    def _eval(self, i, x):
        """Return the zero count that would result from replacing S[i] by x (state unchanged)."""
        S = self.S
        old = S[i]
        others = S[:i] + S[i + 1:]
        before = self.zeros
        self._apply(old, others, -1)
        self._apply(x, others, +1)
        z = self.zeros
        self._apply(x, others, -1)
        self._apply(old, others, +1)
        self.zeros = before
        return z

    def _commit(self, i, x):
        S = self.S
        old = S[i]
        others = S[:i] + S[i + 1:]
        self._apply(old, others, -1)
        self._apply(x, others, +1)
        S[i] = x

    def _step(self):
        self.it += 1
        S, rng, N, d = self.S, self.rng, self.N, self.d
        best = None
        best_z = None
        for _ in range(self.K):
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            z = self._eval(i, x)
            if self.tabu_until[x] > self.it and z >= self.best_zeros:
                continue  # tabu and no aspiration
            if best_z is None or z < best_z or (z == best_z and rng.random() < 0.5):
                best_z, best, best_i, best_x = z, True, i, x
        if best is None:
            return
        old = S[best_i]
        self._commit(best_i, best_x)
        self.tabu_until[old] = self.it + self.TENURE
        if self.zeros < self.best_zeros:
            self.best_zeros = self.zeros
            self.last_improve = self.it
        if self.it - self.last_improve > self.STALL:
            self._restart()

    def run(self, steps, deadline):
        """Advance by up to `steps` moves; return True once S is a difference cover."""
        if self.done:
            return True
        for k in range(steps):
            if self.zeros == 0:
                break
            if (k & 63) == 0 and time.monotonic() > deadline:
                return False
            self._step()
        if self.zeros == 0:
            self.done = True
        return self.done


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
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

    jobs = []                     # dicts: N, mul, inv, st, dead
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
    best_N = lo - 1
    chunk = 400
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Tabu(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    if best is not None:
        return best
    return base_n, base_e
