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


class _Search:
    """Resumable annealing for d distinct elements S with S S^{-1} = G.

    Keeps cnt[g] = number of ordered pairs (a, b) in S x S with a b^{-1} = g,
    and zeros = number of g with cnt[g] == 0. A single-element swap then costs
    O(d) instead of O(d^2), and the state persists across time slices.
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
        """Advance the search by up to `steps` moves; return True once S is a difference cover."""
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


# ------------------------------------------- NEW: two-orbit voltage annealing
#
# Four base vertices: A0, A1 (ids 0, 1) and B0, B1 (ids 2, 3). The base
# multigraph is the 2x2 pattern [[p, d-p], [d-p, p]], so every base vertex has
# degree d. Each dart carries a voltage in a group G of order N, and the lift
# has 4N vertices. A simulated-annealing walk changes one voltage at a time and
# minimises lib.bad_pairs (pairs at distance > 3). This reaches orders 4N, which
# the single-orbit difference-cover search cannot.

def _orbit_anneal(d, N, rng, deadline):
    """Try to find a 4N-vertex lift with diameter 3; return (n, edges) or None."""
    groups = _group_list(N, rng)
    _, mul, _ = rng.choice(groups)
    p = rng.randrange(d + 1)
    pattern = [(0, 2, p), (0, 3, d - p), (1, 2, d - p), (1, 3, p)]
    slots = []
    for u, v, m in pattern:
        slots += [(u, v)] * m
    if not slots:
        return None
    g = [rng.randrange(N) for _ in slots]

    def build_edges(gs):
        return lib.group_lift(4, [(u, v, gg) for (u, v), gg in zip(slots, gs)], N, mul)

    n, e = build_edges(g)
    cur = lib.bad_pairs(n, e, 3)
    T = 1.0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(len(slots))
        old = g[i]
        g[i] = rng.randrange(N)
        n, e = build_edges(g)
        new = lib.bad_pairs(n, e, 3)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            g[i] = old
        T = max(0.15, T * 0.9995)
    n, e = build_edges(g)
    if lib.is_valid(n, e, d, 3):
        return n, e
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + usable
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    # ---- Phase 1: single-orbit difference-cover search (parent method).
    diff_deadline = start + 0.45 * usable
    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers

    best = None                   # (n, edges)
    best_N = lo - 1
    if lo <= hi:
        jobs = []
        for N in range(hi, lo - 1, -1):
            if N < d:
                continue
            for _order, mul, inv in _group_list(N, rng):
                jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

        chunk = 1500
        T = 0.6
        while jobs and time.monotonic() < diff_deadline:
            for job in list(jobs):
                if time.monotonic() >= diff_deadline:
                    break
                if job["N"] <= best_N or job["dead"]:
                    continue
                if job["st"] is None:
                    R = _ratio_table(job["N"], job["mul"], job["inv"])
                    job["st"] = _Search(job["N"], R, d, rng)
                st = job["st"]
                if st.run(chunk, diff_deadline, T):
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                    if n > base_n and lib.is_valid(n, edges, d, D):
                        best = (n, edges)
                        best_N = job["N"]
                        break
                    job["dead"] = True
            jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    # ---- Phase 2: two-orbit voltage annealing, aiming above the current best.
    cur_n, cur_e = best if best is not None else (base_n, base_e)
    N = cur_n // 4 + 1
    Nmax = lib.moore_bound(d, 3) // 4
    while N <= Nmax and time.monotonic() < deadline:
        now = time.monotonic()
        attempt_deadline = min(deadline, now + 0.5 * (deadline - now))
        res = _orbit_anneal(d, N, rng, attempt_deadline)
        if res is None:
            break
        n, e = res
        if n > cur_n:
            cur_n, cur_e = n, e
        N += 1

    if lib.is_valid(cur_n, cur_e, d, D):
        return cur_n, cur_e
    return base_n, base_e
