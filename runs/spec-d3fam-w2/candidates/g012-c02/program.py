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
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 exactly when
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# which gives order 2|G| with |G| <= d(d-1)+1.
#
# New in this version: TARGETED REPAIR MOVES. Instead of proposing a uniformly
# random replacement element, pick an uncovered group element g (cnt[g] == 0)
# and a current member y of S. The element x = g*y satisfies x y^{-1} = g, so
# inserting x directly covers g. The best of several such (position, x) swaps
# is taken with a Metropolis rule. Normalisation: translating S by a right
# multiplication leaves S S^{-1} unchanged, so we keep the identity in S at
# index 0 and never move it.

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


class _TargetedSearch:
    """Resumable search for d elements S (identity at S[0]) with S S^{-1} = G.

    cnt[g] counts ordered pairs (a, b) in S x S with a b^{-1} = g.
    zeros counts g with cnt[g] == 0 (the uncovered elements).
    """

    def __init__(self, N, R, mul, d, rng):
        self.N = N
        self.R = R
        self.mul = mul
        self.d = d
        self.rng = rng
        self.S = []
        self.cnt = [0] * N
        self.zeros = N
        self.done = False
        self.best_zeros = N
        self.stall = 0
        self._reset()

    def _reset(self):
        """Random restart with identity fixed in S."""
        self.S = [0] + self.rng.sample(range(1, self.N), self.d - 1)
        self.cnt = [0] * self.N
        for a in self.S:
            for b in self.S:
                self.cnt[self.R[a][b]] += 1
        self.zeros = sum(1 for c in self.cnt if c == 0)
        self.done = self.zeros == 0
        self.best_zeros = self.zeros
        self.stall = 0

    def _remove(self, x, others):
        cnt, R = self.cnt, self.R
        Rx = R[x]
        for g in [Rx[x]] + [Rx[b] for b in others] + [R[b][x] for b in others]:
            cnt[g] -= 1
            if cnt[g] == 0:
                self.zeros += 1

    def _add(self, x, others):
        cnt, R = self.cnt, self.R
        Rx = R[x]
        for g in [Rx[x]] + [Rx[b] for b in others] + [R[b][x] for b in others]:
            if cnt[g] == 0:
                self.zeros -= 1
            cnt[g] += 1

    def _swap(self, i, x):
        """Replace S[i] by x (x not in S) and update the counts."""
        S = self.S
        old = S[i]
        others = S[:i] + S[i + 1:]
        self._remove(old, others)
        self._add(x, others)
        S[i] = x
        return old

    def _swap_delta(self, i, x):
        """Change in zeros if S[i] were replaced by x; the state is left unchanged."""
        before = self.zeros
        old = self._swap(i, x)
        delta = self.zeros - before
        self._swap(i, old)
        return delta

    def _step(self, T):
        S, rng, N = self.S, self.rng, self.N
        uncovered = [h for h in range(N) if self.cnt[h] == 0]
        if not uncovered:
            return
        g = rng.choice(uncovered)
        cands = []
        for y in S:
            x = self.mul(g, y)          # x * y^{-1} = g covers g directly
            if x in S:
                continue
            for i in range(1, self.d):  # never move the identity at index 0
                cands.append((i, x))
        if not cands:
            return
        if len(cands) > 12:
            cands = rng.sample(cands, 12)
        rng.shuffle(cands)
        best = None
        for i, x in cands:
            dl = self._swap_delta(i, x)
            if best is None or dl < best[0]:
                best = (dl, i, x)
        dl, i, x = best
        if dl <= 0 or rng.random() < math.exp(-dl / T):
            self._swap(i, x)

    def run(self, steps, deadline, T):
        """Advance by up to `steps` moves; return True once S is a difference cover."""
        if self.done:
            return True
        for k in range(steps):
            if self.zeros == 0:
                break
            if (k & 15) == 0 and time.monotonic() > deadline:
                return False
            self._step(T)
            if self.zeros < self.best_zeros:
                self.best_zeros = self.zeros
                self.stall = 0
            else:
                self.stall += 1
                if self.stall > 5000:
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

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    jobs = []                     # dicts: N, mul, inv, st (search state or None)
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None                   # (n, edges)
    best_N = lo - 1
    chunk = 300                   # moves per job per round-robin visit
    T = 0.5

    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _TargetedSearch(job["N"], R, job["mul"], d, rng)
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
