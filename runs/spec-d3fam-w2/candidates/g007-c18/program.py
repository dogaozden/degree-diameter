import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: trivial, cycle, PG(2,q), Araujo-Pardo-Lopez, or K_{d,d}."""
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
            return lib.araujo_lopez_graph(d - 2)        # record family
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 when
# S S^{-1} = G, so we need a difference cover of size d in a group G of
# order N, giving order 2N with N <= d(d-1)+1.

def _group_list(N, rng, per_k=4):
    """Cyclic group of order N plus several semidirect products Z_m x| Z_k."""
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
        for r in rs[:per_k]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving e.

    Pairs are (e,e), (e,o), (o,e) for o in others. Returns the change in the
    number of zero entries of cnt.
    """
    change = 0
    row = R[e]
    gs = [row[e]] + [row[o] for o in others] + [R[o][e] for o in others]
    if sign > 0:
        for g in gs:
            if cnt[g] == 0:
                change -= 1
            cnt[g] += 1
    else:
        for g in gs:
            cnt[g] -= 1
            if cnt[g] == 0:
                change += 1
    return change


class _Task:
    """Resumable simulated-annealing search for a difference cover in one group."""

    RESTART = 150000
    TEMP = 0.45

    def __init__(self, N, mul, inv, d, rng):
        self.N = N
        self.d = d
        self.rng = rng
        self.R = _ratio_table(N, mul, inv)
        self.S = [0] * d
        self.cnt = [0] * N
        self.zeros = N
        self.steps = 0
        self.reset()

    def reset(self):
        """Fresh random state, updated in place so cached references stay valid."""
        N, d, R = self.N, self.d, self.R
        self.S[:] = self.rng.sample(range(N), d)
        self.cnt[:] = [0] * N
        for a in self.S:
            for b in self.S:
                self.cnt[R[a][b]] += 1
        self.zeros = self.cnt.count(0)
        self.steps = 0

    def advance(self, budget):
        """Run up to `budget` moves. Return a cover (list) if found, else None."""
        if self.zeros == 0:
            return list(self.S)
        R, cnt, S = self.R, self.cnt, self.S
        N, d, rng = self.N, self.d, self.rng
        inS = set(S)
        for _ in range(budget):
            self.steps += 1
            if self.steps > self.RESTART:
                self.reset()
                inS = set(S)
                continue
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in inS:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            z = (self.zeros
                 + _pair_update(cnt, R, old, others, -1)
                 + _pair_update(cnt, R, x, others, 1))
            if z <= self.zeros or rng.random() < math.exp(-(z - self.zeros) / self.TEMP):
                S[i] = x
                inS.discard(old)
                inS.add(x)
                self.zeros = z
                if z == 0:
                    return list(S)
            else:
                _pair_update(cnt, R, x, others, -1)
                _pair_update(cnt, R, old, others, 1)
        return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 3.0)
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

    # Only the diameter-3 regime is searched.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: PG(2, d-1) incidence is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Difference-cover group lifts: order 2N needs N > best_n / 2.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    if lo > hi:
        return best

    def candidates():
        """Yield (N, mul, inv) for N ascending, so smaller orders are tried first."""
        for N in range(lo, hi + 1):
            gl = _group_list(N, rng)
            rng.shuffle(gl)
            for g in gl:
                yield N, g[1], g[2]

    STEPS = 2000
    POOL = 12
    cand = candidates()
    pool = []
    exhausted = False

    while time.monotonic() < deadline:
        while len(pool) < POOL and not exhausted:
            try:
                N, mul, inv = next(cand)
            except StopIteration:
                exhausted = True
                break
            if 2 * N <= best_n:
                continue
            pool.append(_Task(N, mul, inv, d, rng))
        if not pool:
            break

        for t in list(pool):
            if time.monotonic() >= deadline:
                break
            if 2 * t.N <= best_n:
                pool.remove(t)
                continue
            S = t.advance(STEPS)
            if S is not None:
                try:
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in S], t.N, t.mul)
                    consider(n, edges)
                except Exception:
                    pass
                pool.remove(t)
                pool = [p for p in pool if 2 * p.N > best_n]
                break

    return best
