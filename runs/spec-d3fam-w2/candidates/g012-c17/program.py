import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline graphs used whenever the search fails or is not needed."""
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
# S S^{-1} = G. So we need a "difference cover" S of size d in a group G of
# order N, which gives a graph of order 2N with N <= d(d-1)+1.

def _group_list(N, rng):
    """Cyclic group of order N plus some semidirect products Z_m x| Z_k of order N."""
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

    cnt[g] counts ordered pairs (a, b) in S x S with a b^{-1} = g; zeros is the
    number of uncovered g. A single-element swap costs O(d).
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


def _open_N(N, rng):
    """Job list for one group order N: one job per candidate group."""
    return {
        "jobs": [{"mul": g[1], "inv": g[2], "st": None, "dead": False}
                 for g in _group_list(N, rng)],
        "steps": 0,
        "done": False,
    }


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only diameter 3 with non-Moore-extremal d is searched.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    best_n = base_n

    lo_N = max(best_n // 2 + 1, d)     # need 2N > current best
    hi_N = d * (d - 1) + 1             # hard bound for difference covers
    if lo_N > hi_N:
        return best

    # Window of N values searched round-robin, smallest first (small N is
    # easier to cover, and any success immediately raises the bar).
    W = 4
    chunk = 1500
    step_cap = 1_000_000               # per-N budget before retiring it
    T = 0.6

    state = {}
    active = []
    next_N = lo_N

    def refill():
        nonlocal next_N
        while len(active) < W and next_N <= hi_N:
            N = next_N
            next_N += 1
            if 2 * N > best_n and N >= d:
                state[N] = _open_N(N, rng)
                active.append(N)

    refill()
    while active and time.monotonic() < deadline:
        for N in list(active):
            if time.monotonic() >= deadline:
                break
            info = state[N]
            if info["done"] or 2 * N <= best_n or info["steps"] > step_cap:
                active.remove(N)
                continue
            for job in info["jobs"]:
                if time.monotonic() >= deadline:
                    break
                if job["dead"]:
                    continue
                if job["st"] is None:
                    R = _ratio_table(N, job["mul"], job["inv"])
                    job["st"] = _Search(N, R, d, rng)
                st = job["st"]
                info["steps"] += chunk
                if st.run(chunk, deadline, T):
                    try:
                        n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S],
                                                  N, job["mul"])
                        if n > best_n and lib.is_valid(n, edges, d, D):
                            best = (n, edges)
                            best_n = n
                            info["done"] = True
                            break
                    except Exception:
                        pass
                    job["dead"] = True
            if not info["done"] and all(j["dead"] for j in info["jobs"]):
                info["done"] = True
            if info["done"] and N in active:
                active.remove(N)
        refill()

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
