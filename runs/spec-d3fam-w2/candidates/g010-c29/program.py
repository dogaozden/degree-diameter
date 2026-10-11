import math
import random
import time
from array import array

import lib


def _fallback(d, D):
    """Verified baseline graphs used whenever the search fails."""
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
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 when
# S S^{-1} = G. So the task is a difference cover of size d in a group G,
# giving order 2|G| with |G| <= d(d-1)+1. Degree is exactly d, and there are
# no loops or duplicate edges since S has d distinct elements.

def _group_list(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k of order N."""
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
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """Flat table R[x*N + y] = x * y^{-1}, stored compactly."""
    iv = [inv(y) for y in range(N)]
    R = array("i", [0]) * (N * N)
    for x in range(N):
        base = x * N
        for y in range(N):
            R[base + y] = mul(x, iv[y])
    return R


class _Search:
    """Resumable annealing for d distinct elements S with S S^{-1} = G.

    cnt[g] counts ordered pairs (a, b) in S x S with a b^{-1} = g.
    zeros = number of g with cnt[g] == 0 (the uncovered elements).
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
                self.cnt[R[a * N + b]] += 1
        self.zeros = sum(1 for c in self.cnt if c == 0)
        self.done = self.zeros == 0

    def _apply(self, x, others, sign):
        """Add (sign=+1) or remove (sign=-1) the ordered pairs of x with itself and with others."""
        cnt, R, N = self.cnt, self.R, self.N
        xN = x * N
        gs = [R[xN + x]] + [R[xN + b] for b in others] + [R[b * N + x] for b in others]
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
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    # Only diameter 3 is searched; the Moore-extremal case is already optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return best

    best_n = best[0]
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    lo = max(best_n // 2 + 1, d) # need 2N > best_n

    if lo > hi:
        return best

    # Jobs: one per (N, group). Searched in round-robin, larger N first.
    jobs = []
    for N in range(hi, lo - 1, -1):
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None,
                         "T": rng.uniform(0.35, 0.9), "dead": False})

    chunk = 1500
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if 2 * job["N"] <= best_n or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline, job["T"]):
                try:
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S],
                                              job["N"], job["mul"])
                    if n > best_n and lib.is_valid(n, edges, d, D):
                        best = (n, edges)
                        best_n = n
                        break
                except Exception:
                    pass
                job["dead"] = True
        jobs = [j for j in jobs if 2 * j["N"] > best_n and not j["dead"]]

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return _fallback(d, D)
