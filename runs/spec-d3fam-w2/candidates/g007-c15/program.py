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
# New in this version: a tabu search over swap moves (best of a small sample of
# candidate swaps, with a recency tabu on removed elements) replaces the
# annealing walk. Group families are broadened to include the direct products
# Z_m x Z_k (r = 1) for every factorisation of N, not only random r values.


def _group_list(N, rng, cap=6):
    """Cyclic group plus up to `cap` non-cyclic groups of order N (r = 1 means direct product)."""
    groups = [lib.cyclic_group(N)]
    others = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in [1] + rs[:3]:
            others.append((m, k, r))
    rng.shuffle(others)
    for m, k, r in others[:cap]:
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
    """Resumable tabu search for d distinct elements S with S S^{-1} = G.

    cnt[g] = number of ordered pairs (a, b) in S x S with a b^{-1} = g;
    zeros = number of g with cnt[g] == 0 (the number of uncovered elements).
    Each move is scored exactly in O(d) by apply/revert.
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
        self.tabu = {}
        self.it = 0
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

    def _move(self, i, x):
        """Replace S[i] by x permanently."""
        S = self.S
        old = S[i]
        others = S[:i] + S[i + 1:]
        self._apply(old, others, -1)
        self._apply(x, others, +1)
        S[i] = x
        self.tabu[old] = self.it + self.tenure

    def _iterate(self, K):
        S, rng, N, d = self.S, self.rng, self.N, self.d
        best = None
        for _ in range(K):
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            before = self.zeros
            self._apply(old, others, -1)
            self._apply(x, others, +1)
            delta = self.zeros - before
            self._apply(x, others, -1)
            self._apply(old, others, +1)
            tabu_hit = self.tabu.get(x, -1) > self.it
            # Aspiration: a tabu move is allowed if it would finish the cover.
            if tabu_hit and not (self.zeros + delta == 0):
                continue
            if best is None or delta < best[0] or (delta == best[0] and rng.random() < 0.5):
                best = (delta, i, x)
        if best is not None:
            _, i, x = best
            self._move(i, x)

    def run(self, iters, deadline, K=6, tenure=None):
        """Advance by up to `iters` tabu iterations; return True once S is a difference cover."""
        if self.done:
            return True
        self.tenure = tenure if tenure is not None else max(3, self.d // 2)
        for _ in range(iters):
            if self.zeros == 0:
                break
            if (self.it & 63) == 0 and time.monotonic() > deadline:
                return False
            self._iterate(K)
            self.it += 1
        if self.zeros == 0:
            self.done = True
        return self.done


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
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

    jobs = []                     # dicts: N, mul, inv, st (search state or None)
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for mul_inv in _group_list(N, rng):
            _order, mul, inv = mul_inv
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None                   # (n, edges)
    best_N = lo - 1
    chunk = 300                   # tabu iterations per job per round-robin visit

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
