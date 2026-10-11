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

# ------------------------------------------- NEW: multiplier-orbit covers
#
# For the cyclic group Z_N, choose a unit t and restrict S to be a union of
# orbits of x -> t*x (mod N). Covering then only needs checking on the
# difference multiset, and the search space shrinks from C(N, d) to the
# (much smaller) set of orbit combinations. Hill-climbing swaps orbits of
# equal size, so the total size stays exactly d and S stays a set of d
# distinct elements.

def _orbit_classes(N, t):
    """Orbits of x -> t*x mod N on Z_N (t a unit), as lists of residues."""
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
            y = (y * t) % N
        orbits.append(orb)
    return orbits


def _uncovered(N, S):
    """Number of residues g in Z_N not of the form a - b with a, b in S."""
    cov = set()
    for a in S:
        for b in S:
            cov.add((a - b) % N)
    return N - len(cov)


def _random_orbit_selection(orbits, d, rng):
    """Random list of orbit indices whose sizes sum exactly to d, or None."""
    for _ in range(60):
        idx = list(range(len(orbits)))
        rng.shuffle(idx)
        chosen, tot = [], 0
        for i in idx:
            if tot + len(orbits[i]) <= d:
                chosen.append(i)
                tot += len(orbits[i])
                if tot == d:
                    return chosen
    return None


def _orbit_cover_search(N, d, t, rng, iters):
    """Hill-climb over unions of t-orbits with total size d; return S covering Z_N, or None."""
    orbits = _orbit_classes(N, t)
    sel = _random_orbit_selection(orbits, d, rng)
    if sel is None:
        return None

    def elems(chosen):
        return [x for i in chosen for x in orbits[i]]

    cur = _uncovered(N, elems(sel))
    for _ in range(iters):
        if cur == 0:
            break
        pos = rng.randrange(len(sel))
        s = len(orbits[sel[pos]])
        in_sel = set(sel)
        cands = [j for j in range(len(orbits)) if j not in in_sel and len(orbits[j]) == s]
        if not cands:
            continue
        new = sel[:]
        new[pos] = rng.choice(cands)
        val = _uncovered(N, elems(new))
        if val <= cur or rng.random() < 0.05:
            sel, cur = new, val
    if cur == 0:
        return elems(sel)
    return None


def _multiplicative_order(t, N):
    r, x = 1, t % N
    while x != 1:
        x = (x * t) % N
        r += 1
        if r > N:
            return None
    return r


def _orbit_phase(d, base_n, rng, lo, hi, deadline):
    """Try cyclic groups with multiplier-orbit covers, largest order first."""
    for N in range(hi, lo - 1, -1):
        if time.monotonic() >= deadline:
            break
        if N < d:
            continue
        units = [t for t in range(2, N) if math.gcd(t, N) == 1]
        if not units:
            continue
        rng.shuffle(units)
        tried = 0
        for t in units:
            if time.monotonic() >= deadline or tried >= 40:
                break
            if _multiplicative_order(t, N) is None:
                continue
            tried += 1
            S = _orbit_cover_search(N, d, t, rng, 400)
            if S is None:
                continue
            mul = lib.cyclic_group(N)[1]
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > base_n and lib.is_valid(n, edges, d, 3):
                return n, edges
            break
    return None


# ------------------------------------- parent: annealing over difference covers

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


def _anneal_phase(d, base_n, rng, best_N, hi, deadline):
    """Annealing over all group orders above best_N; return (n, edges) or None."""
    jobs = []
    for N in range(hi, best_N, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
    cur_best_N = best_N
    chunk = 1500
    T = 0.6

    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= cur_best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline, T):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, 3):
                    best = (n, edges)
                    cur_best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > cur_best_N and not j["dead"]]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + usable
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

    best = None
    best_N = lo - 1

    # Phase 1: cheap multiplier-orbit search on cyclic groups.
    p1_deadline = start + 0.5 * usable
    res = _orbit_phase(d, base_n, rng, lo, hi, p1_deadline)
    if res is not None:
        best = res
        best_N = res[0] // 2

    # Phase 2: annealing over cyclic and semidirect groups above the current best.
    if time.monotonic() < deadline and best_N < hi:
        r2 = _anneal_phase(d, base_n, rng, best_N, hi, deadline)
        if r2 is not None and (best is None or r2[0] > best[0]):
            best = r2

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
