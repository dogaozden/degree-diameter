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
# NEW HELPER: multiplier-invariant covers in Z_N.
# If u is a unit of Z_N, the orbits {x, ux, u^2x, ...} partition Z_N. A set S
# that is a union of u-orbits is invariant under x -> ux, so S S^{-1} is also
# invariant. The search space then shrinks from C(N, d) to the number of
# orbit compositions of d, and each move only swaps an orbit for another orbit
# of the same size. Cyclotomic-style covers of this kind often reach larger N
# than unstructured annealing does.

def _cyclic_mul(N):
    return lambda x, y: (x + y) % N


def _unit_order(u, N):
    """Multiplicative order of the unit u modulo N."""
    t, y = 1, u % N
    while y != 1:
        y = (y * u) % N
        t += 1
    return t


def _unit_orbits(N, u):
    """Partition Z_N into orbits of x -> u*x."""
    seen = [False] * N
    orbits = []
    for x in range(N):
        if seen[x]:
            continue
        orb = []
        y = x
        while not seen[y]:
            seen[y] = True
            orb.append(y)
            y = (y * u) % N
        orbits.append(orb)
    return orbits


class _OrbitSearch:
    """Annealing over unions of multiplier orbits in cyclic Z_N with |S| = d."""

    def __init__(self, N, orbits, d, rng):
        self.N = N
        self.orbits = orbits
        self.d = d
        self.rng = rng
        self.chosen = self._random_composition()
        self.cost = self._cost(self.chosen) if self.chosen is not None else None
        self.done = self.cost == 0

    def _random_composition(self):
        for _ in range(200):
            chosen, used, rem = [], set(), self.d
            while rem > 0:
                cands = [i for i, o in enumerate(self.orbits)
                         if i not in used and len(o) <= rem]
                if not cands:
                    break
                i = self.rng.choice(cands)
                used.add(i)
                chosen.append(i)
                rem -= len(self.orbits[i])
            if rem == 0:
                return chosen
        return None

    def elements(self):
        return [x for i in self.chosen for x in self.orbits[i]]

    def _cost(self, chosen):
        S = [x for i in chosen for x in self.orbits[i]]
        N = self.N
        diffs = {(a - b) % N for a in S for b in S}
        return N - len(diffs)

    def _step(self, T):
        ch = self.chosen
        j = self.rng.randrange(len(ch))
        s = len(self.orbits[ch[j]])
        cands = [k for k in range(len(self.orbits))
                 if k not in ch and len(self.orbits[k]) == s]
        if not cands:
            return
        k = self.rng.choice(cands)
        new = ch[:j] + [k] + ch[j + 1:]
        c = self._cost(new)
        delta = c - self.cost
        if delta <= 0 or self.rng.random() < math.exp(-delta / T):
            self.chosen = new
            self.cost = c

    def run(self, steps, deadline, T):
        if self.done:
            return True
        if self.chosen is None:
            return False
        for k in range(steps):
            if self.cost == 0:
                break
            if (k & 63) == 0 and time.monotonic() > deadline:
                return False
            self._step(T)
        if self.cost == 0:
            self.done = True
        return self.done


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
    """Resumable annealing for d distinct elements S with S S^{-1} = G."""

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

    def elements(self):
        return self.S

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
    deadline = start + max(1.0, 0.82 * time_limit - 2.0)
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

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        # Multiplier-invariant cyclic jobs (new helper).
        units = []
        for u in range(2, N):
            if math.gcd(u, N) == 1:
                t = _unit_order(u, N)
                if 2 <= t <= d:
                    units.append((t, u))
        rng.shuffle(units)
        seen_orders = set()
        for t, u in units:
            if t in seen_orders and len(seen_orders) < 3:
                continue
            seen_orders.add(t)
            orbits = _unit_orbits(N, u)
            jobs.append({"kind": "orb", "N": N, "mul": _cyclic_mul(N),
                         "orbits": orbits, "st": None, "dead": False})
            if len(seen_orders) >= 3:
                break
        # Unstructured group jobs (as in the parent).
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"kind": "grp", "N": N, "mul": mul, "inv": inv,
                         "st": None, "dead": False})

    best = None
    best_N = lo - 1
    T = 0.5

    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            N = job["N"]
            if job["st"] is None:
                if job["kind"] == "grp":
                    R = _ratio_table(N, job["mul"], job["inv"])
                    job["st"] = _Search(N, R, d, rng)
                else:
                    job["st"] = _OrbitSearch(N, job["orbits"], d, rng)
                    if job["st"].chosen is None:
                        job["dead"] = True
                        continue
            st = job["st"]
            chunk = 1500 if job["kind"] == "grp" else 300
            if st.run(chunk, deadline, T):
                S = st.elements()
                try:
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in S],
                                              N, job["mul"])
                except Exception:
                    job["dead"] = True
                    continue
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = N
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
