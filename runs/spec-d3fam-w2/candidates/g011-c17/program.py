import math
import random
import time

import numpy as np

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


# ------------------------------------------------ multi-orbit group lifts
#
# A "k-orbit lift": k A-vertices and k B-vertices, each carrying a group G of
# order N, for 2kN vertices in total. Each of the d "layers" t is a permutation
# sigma_t of {0..k-1} plus a voltage g_{t,i} in G per A-vertex i. The lift has
# edges (A_i, x) -- (B_{sigma_t(i)}, x * g_{t,i}). Every vertex then has
# degree exactly d. k = 1 recovers the Cayley-type difference-cover lifts.
#
# Left translations are automorphisms, so distances from (u, x) equal distances
# from (u, e). It is therefore enough to check diameter from the 2k identity
# representatives. The search is simulated annealing on the number of
# unreached (source, target) pairs, using only these 2k BFS runs in numpy.


def _group_specs(N, rng):
    """Cyclic Z_N plus up to two semidirect products Z_m x| Z_k of order N."""
    specs = [("cyc", N)]
    sds = []
    for kk in range(2, N + 1):
        if N % kk:
            continue
        m = N // kk
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m]
        if rs:
            rng.shuffle(rs)
            sds.append(("sd", m, kk, rs[0]))
    rng.shuffle(sds)
    specs += sds[:2]
    return specs


def _tables(spec):
    """Return (mulT, invT) as numpy tables for a group spec; identity is element 0."""
    if spec[0] == "cyc":
        N = spec[1]
        x = np.arange(N, dtype=np.int64)
        return (x[:, None] + x[None, :]) % N, (-x) % N
    _, m, kk, r = spec
    order, mul, inv = lib.semidirect_group(m, kk, r)
    mt = np.array([[mul(a, b) for b in range(order)] for a in range(order)],
                  dtype=np.int64)
    iv = np.array([inv(a) for a in range(order)], dtype=np.int64)
    return mt, iv


class _Lift:
    """State of a k-orbit lift over a group of order N, annealed toward diameter D."""

    T = 0.8

    def __init__(self, k, N, tables, d, D, rng):
        self.k, self.N, self.d, self.D = k, N, d, D
        self.mulT, self.invT = tables
        self.n = 2 * k * N
        self.rng = rng
        self.perm = [rng.sample(range(k), k) for _ in range(d)]
        self.volt = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
        self.nb = np.zeros((self.n, d), dtype=np.int64)
        for t in range(d):
            self._refresh(t)
        self.f = self._score()

    def _refresh(self, t):
        """Recompute column t of the neighbour table from perm[t] and volt[t]."""
        k, N = self.k, self.N
        perm, volt, nb = self.perm[t], self.volt[t], self.nb
        for i in range(k):
            j = perm[i]
            g = volt[i]
            nb[i * N:(i + 1) * N, t] = (k + j) * N + self.mulT[:, g]
            nb[(k + j) * N:(k + j + 1) * N, t] = i * N + self.mulT[:, self.invT[g]]

    def _score(self):
        """Total number of vertices not reached within D steps from the 2k identity representatives."""
        n, D, nb = self.n, self.D, self.nb
        total = 0
        for b in range(2 * self.k):
            s = b * self.N
            seen = np.zeros(n, dtype=bool)
            seen[s] = True
            front = np.array([s], dtype=np.int64)
            for _ in range(D):
                nxt = nb[front].ravel()
                nxt = np.unique(nxt[~seen[nxt]])
                if nxt.size == 0:
                    break
                seen[nxt] = True
                front = nxt
            total += n - int(seen.sum())
        return total

    def _move(self):
        rng = self.rng
        t = rng.randrange(self.d)
        old_col = self.nb[:, t].copy()
        old_perm = self.perm[t][:]
        old_volt = self.volt[t][:]
        if self.k > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(self.k), 2)
            self.perm[t][a], self.perm[t][b] = self.perm[t][b], self.perm[t][a]
        else:
            self.volt[t][rng.randrange(self.k)] = rng.randrange(self.N)
        self._refresh(t)
        f_new = self._score()
        delta = f_new - self.f
        if delta <= 0 or rng.random() < math.exp(-delta / self.T):
            self.f = f_new
        else:
            self.nb[:, t] = old_col
            self.perm[t] = old_perm
            self.volt[t] = old_volt

    def run(self, steps):
        """Advance by up to `steps` moves; return True once the lift has diameter <= D."""
        for _ in range(steps):
            if self.f == 0:
                return True
            self._move()
        return self.f == 0

    def edges(self):
        """Return (n, edges) of the current lift, deduplicated."""
        s = set()
        for v in range(self.n):
            for u in self.nb[v].tolist():
                if u != v:
                    s.add((min(u, v), max(u, v)))
        return self.n, sorted(s)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    moore = lib.moore_bound(d, D)
    if D < 3 or d < 3 or base_n >= moore:
        return base_n, base_e

    cap = min(moore, 3000)
    cands = []
    for k in (1, 2, 3):
        for N in range(2, cap // (2 * k) + 1):
            order = 2 * k * N
            if base_n < order <= cap:
                cands.append((order, k, N))
    cands.sort()
    cands = cands[:100]

    jobs = []
    for order, k, N in cands:
        for spec in _group_specs(N, rng):
            jobs.append({"k": k, "N": N, "order": order, "spec": spec,
                         "st": None, "done": False})
    jobs = jobs[:300]

    best = None
    best_n = base_n
    CHUNK = 300

    try:
        while jobs and time.monotonic() < deadline:
            for job in jobs:
                if time.monotonic() >= deadline:
                    break
                if job["done"] or job["order"] <= best_n:
                    continue
                if job["st"] is None:
                    tables = _tables(job["spec"])
                    job["st"] = _Lift(job["k"], job["N"], tables, d, D, rng)
                st = job["st"]
                if st.run(CHUNK):
                    n, e = st.edges()
                    if n > best_n and lib.is_valid(n, e, d, D):
                        best = (n, e)
                        best_n = n
                    job["done"] = True
            jobs = [j for j in jobs if not j["done"] and j["order"] > best_n]
    except Exception:
        pass

    if best is not None:
        return best
    return base_n, base_e
