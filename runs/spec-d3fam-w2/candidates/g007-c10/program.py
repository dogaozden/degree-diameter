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
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 whenever
# S S^{-1} = G. So the task is a difference cover of size d in a group G,
# giving order 2|G| with |G| <= d(d-1)+1 (the bipartite Moore bound).
#
# Search change: instead of a blind annealing swap, each move re-places one
# element with the best of a random sample of candidates (min-conflicts),
# with a small random-walk noise. Groups include non-cyclic abelian products
# (r = 1) as well as several non-abelian semidirect products per order.

def _groups(N, rng, limit=6):
    """Candidate groups of order N: cyclic, abelian Z_m x Z_k (r = 1), and some semidirect products."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        chosen = []
        if 1 in rs:
            chosen.append(1)
        others = [r for r in rs if r != 1]
        rng.shuffle(others)
        chosen += others[:3]
        for r in chosen:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    rng.shuffle(groups)
    return groups[:limit]


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


class _MinConflictSearch:
    """Min-conflicts search for d distinct elements S with S S^{-1} = G.

    cnt[g] = number of ordered pairs (a, b) in S x S with a b^{-1} = g;
    zeros = number of g with cnt[g] == 0 (the number of uncovered elements).
    """

    def __init__(self, N, R, d, rng, samples=30, noise=0.02):
        self.N = N
        self.R = R
        self.d = d
        self.rng = rng
        self.samples = samples
        self.noise = noise
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
        rng = self.rng
        i = rng.randrange(self.d)
        old = S[i]
        others = S[:i] + S[i + 1:]
        self._apply(old, others, -1)

        if rng.random() < self.noise:
            while True:
                x = rng.randrange(self.N)
                if x not in S:
                    break
            S[i] = x
            self._apply(x, others, +1)
            return

        best_x, best_z = None, None
        for _ in range(self.samples):
            x = rng.randrange(self.N)
            if x in S:
                continue
            self._apply(x, others, +1)
            z = self.zeros
            self._apply(x, others, -1)
            if best_z is None or z < best_z or (z == best_z and rng.random() < 0.5):
                best_z, best_x = z, x
        if best_x is None:
            best_x = old
        S[i] = best_x
        self._apply(best_x, others, +1)

    def run(self, steps, deadline):
        """Advance by up to `steps` moves; return True once S is a difference cover."""
        if self.done:
            return True
        for k in range(steps):
            if self.zeros == 0:
                break
            if (k & 63) == 0 and time.monotonic() > deadline:
                break
            self._step()
        if self.zeros == 0:
            self.done = True
        return self.done


def _job_stream(lo, hi, d, rng):
    """Yield (N, mul, inv) for all candidate groups, from largest order down."""
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _groups(N, rng):
            yield N, mul, inv


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # bipartite Moore bound for diameter 3
    if lo > hi:
        return base_n, base_e

    stream = _job_stream(lo, hi, d, rng)
    ACTIVE = 24                   # number of jobs time-sliced at once
    MAX_STEPS = 60000             # give up on a job after this many moves
    chunk = 400
    active = []
    best = None
    best_N = lo - 1

    def refill():
        while len(active) < ACTIVE:
            try:
                N, mul, inv = next(stream)
            except StopIteration:
                return
            active.append({"N": N, "mul": mul, "inv": inv,
                           "st": None, "steps": 0, "dead": False})

    while time.monotonic() < deadline:
        refill()
        if not active:
            break
        for job in list(active):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _MinConflictSearch(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S],
                                          job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
            else:
                job["steps"] += chunk
                if job["steps"] >= MAX_STEPS:
                    job["dead"] = True
            job["st"] = job["st"] if not job["dead"] else None
        active = [j for j in active if not j["dead"] and j["N"] > best_N]

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
