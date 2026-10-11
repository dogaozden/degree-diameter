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
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ phase 1: Cayley difference covers
# Two base vertices, graph on G x {0,1}, a_x ~ b_{x s} for s in S.
# Diameter <= 3 exactly when S S^{-1} = G.

def _group_list(N, rng):
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


def _cayley(d, lo, hi, rng, deadline):
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
    best_N = lo - 1
    chunk = 1500
    T = 0.6
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline, T):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if lib.is_valid(n, edges, d, 3):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


# ------------------------------------------- phase 2: 2+2 base voltage lifts
# Base: A0, A1 (fiber 0, 1) and B0, B1 (fibers 2, 3), each lifted to a group G
# of order m, so n = 4m. Darts A_i-B_j carry voltage sets S_ij in G with
# |S_00| = |S_11| = a, |S_01| = |S_10| = d - a, so every vertex has degree d.
# Left multiplication by G is an automorphism, so diameter <= 3 iff the
# eccentricity of the four fibre representatives (x = 0) is <= 3.

def _divisors(M):
    return [k for k in range(1, M + 1) if M % k == 0]


def _groups_of_order(M, rng):
    groups = [lib.cyclic_group(M)]
    for k in _divisors(M):
        if k < 2:
            continue
        mm = M // k
        if mm < 2:
            continue
        rs = [r for r in range(1, mm)
              if math.gcd(r, mm) == 1 and pow(r, k, mm) == 1 % mm]
        rng.shuffle(rs)
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(mm, k, r))
            except ValueError:
                pass
    return groups


_KEYS = ((0, 0), (1, 1), (0, 1), (1, 0))


def _adj(m, sets, tab):
    adj = [[] for _ in range(4 * m)]
    for (i, j), S in sets.items():
        bj = (2 + j) * m
        for g in S:
            for x in range(m):
                u = i * m + x
                v = bj + tab[x][g]
                adj[u].append(v)
                adj[v].append(u)
    return adj


def _bad(adj, m):
    """Sum over the four fibre representatives of the number of vertices at distance > 3."""
    total = 0
    for rep in (0, m, 2 * m, 3 * m):
        seen = {rep}
        frontier = [rep]
        for _ in range(3):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if v not in seen:
                        seen.add(v)
                        nxt.append(v)
            frontier = nxt
        total += 4 * m - len(seen)
    return total


def _lift_search(m, d, D, rng, deadline):
    groups = _groups_of_order(m, rng)
    TEMP = 0.5
    while time.monotonic() < deadline:
        _o, mul, _inv = rng.choice(groups)
        tab = [[mul(x, g) for g in range(m)] for x in range(m)]
        a = rng.randint(1, d - 1)
        sizes = {(0, 0): a, (1, 1): a, (0, 1): d - a, (1, 0): d - a}
        sets = {k: rng.sample(range(m), sizes[k]) for k in _KEYS}
        f = _bad(_adj(m, sets, tab), m)
        stall = 0
        while f > 0 and time.monotonic() < deadline and stall < 4000:
            key = _KEYS[rng.randrange(4)]
            S = sets[key]
            idx = rng.randrange(len(S))
            new = rng.randrange(m)
            if new in S:
                stall += 1
                continue
            old = S[idx]
            S[idx] = new
            f2 = _bad(_adj(m, sets, tab), m)
            if f2 <= f or rng.random() < math.exp(-(f2 - f) / TEMP):
                if f2 < f:
                    stall = 0
                else:
                    stall += 1
                f = f2
            else:
                S[idx] = old
                stall += 1
        if f == 0:
            edges = []
            for (i, j), S in sets.items():
                bj = (2 + j) * m
                for g in S:
                    for x in range(m):
                        edges.append((i * m + x, bj + tab[x][g]))
            n = 4 * m
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def _lift_phase(d, D, rng, cur_n, deadline):
    best = None
    m = cur_n // 4 + 1
    hi = (d * (d - 1) + 1) // 2
    while m <= hi and time.monotonic() < deadline:
        now = time.monotonic()
        dl = now + 0.6 * (deadline - now)
        res = _lift_search(m, d, D, rng, dl)
        if res is None:
            break
        best = res
        m += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)

    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo <= hi:
        c = _cayley(d, lo, hi, rng, start + 0.4 * total)
        if c is not None and c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
            best = c

    k2 = _lift_phase(d, D, rng, best[0], deadline)
    if k2 is not None and k2[0] > best[0] and lib.is_valid(k2[0], k2[1], d, D):
        best = k2

    return best
