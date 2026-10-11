import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


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
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


class _Search:
    """Resumable annealing for d distinct elements S with S S^{-1} = G.

    cnt[g] counts ordered pairs (a, b) in S x S with a b^{-1} = g; zeros counts
    uncovered g. A single swap costs O(d), and the state persists across slices.
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


def _find_cover(N, d, rng, soft, hard):
    """Search groups of order N for a d-element difference cover; return (mul, S) or None.

    Round-robins over candidate groups, with restarts so no single run stalls.
    Stops at `soft` (per-order budget) or `hard` (global deadline).
    """
    deadline = min(soft, hard)
    jobs = [{"mul": g[1], "inv": g[2], "R": None, "st": None, "used": 0}
            for g in _group_list(N, rng)]
    if not jobs:
        return None
    chunk = 2000
    restart_limit = 300000
    while True:
        for job in jobs:
            if time.monotonic() >= deadline:
                return None
            if job["st"] is None:
                if job["R"] is None:
                    job["R"] = _ratio_table(N, job["mul"], job["inv"])
                job["st"] = _Search(N, job["R"], d, rng, rng.uniform(0.35, 0.9))
                job["used"] = 0
            st = job["st"]
            if st.run(chunk, deadline):
                return job["mul"], list(st.S)
            job["used"] += chunk
            if job["used"] > restart_limit:
                job["st"] = None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2 (instant baseline).
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Difference-cover group lifts: order 2N needs S S^{-1} = G with |S| = d.
    # Search N ascending; each success raises the bar, and a failure at N
    # means larger N is even harder, so stop there.
    hi = d * (d - 1) + 1
    lo = max(d, best_n // 2 + 1)
    for N in range(lo, hi + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        if 2 * N <= best_n:
            continue
        remaining = deadline - now
        found = _find_cover(N, d, rng, now + 0.6 * remaining, deadline)
        if found is None:
            break
        mul, S = found
        try:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
