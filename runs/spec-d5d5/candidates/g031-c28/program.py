import itertools
import math
import random
import time

import lib

ITERS = 600          # annealing moves per random restart of one connection set
SLICE = 150          # moves per job per round-robin turn
MAX_GROUPS = 12     # groups tried per order in the fallback phase
PER_GROUP = 2400     # moves spent on one group in the fallback phase
PHASE_A_FRAC = 0.5   # share of the search time spent trying orders above the known record
# Known record half-orders (order / 2) for specific cases; the search targets above these.
KNOWN_HALF = {(5, 5): 168}   # record order 336 = 2 * 168


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


class _Job:
    """Resumable simulated annealing over connection sets S for one (N, group) pair."""

    def __init__(self, N, m, k, r, d, D, rng):
        _, mul, inv = lib.semidirect_group(m, k, r)
        self.N = N
        self.d = d
        self.D = D
        self.rng = rng
        self.T = [[mul(x, g) for g in range(N)] for x in range(N)]
        self.invs = [inv(g) for g in range(N)]
        self.done = False
        self.result = None
        self._restart()

    def _restart(self):
        self.S = [0] + self.rng.sample(range(1, self.N), self.d - 1)
        self.cur = _unreached(self.N, self.T, self.invs, self.S, self.D)
        self.it = 0

    def step(self, steps):
        """Run up to `steps` annealing moves; return True once a connection set with diameter <= D is found."""
        for _ in range(steps):
            if self.cur == 0:
                break
            if self.it >= ITERS:
                self._restart()
                continue
            temp = max(0.05, 2.0 * (1.0 - self.it / ITERS))
            self.it += 1
            i = self.rng.randrange(1, self.d)
            c = self.rng.randrange(1, self.N)
            if c in self.S:
                continue
            S2 = self.S[:]
            S2[i] = c
            v = _unreached(self.N, self.T, self.invs, S2, self.D)
            if v <= self.cur or self.rng.random() < math.exp(-(v - self.cur) / temp):
                self.S, self.cur = S2, v
        if self.cur == 0:
            self.done = True
            self.result = self.S
            return True
        return False


def _edges(N, T, S):
    """Edge list of the bi-Cayley graph with A_x = x and B_y = N + y."""
    return [(x, N + T[x][g]) for x in range(N) for g in S]


def _phase_a(d, D, rng, lo, top, deadline, consider):
    """Round-robin annealing over all groups for orders in [lo, top], to beat the known record."""
    alive = []
    for N in range(top, lo - 1, -1):
        for m, k, r in _groups(N):
            alive.append(_Job(N, m, k, r, d, D, rng))
    while alive and time.monotonic() < deadline:
        keep = []
        for job in alive:
            if time.monotonic() >= deadline:
                break
            if job.step(SLICE):
                consider(2 * job.N, _edges(job.N, job.T, job.result))
            else:
                keep.append(job)
        alive = keep


def _phase_b(d, D, rng, start_N, deadline, consider):
    """Descending search over orders from start_N, a few groups per order, as a fallback."""
    for N in range(start_N, d, -1):
        if time.monotonic() >= deadline:
            return
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() >= deadline:
                return
            job = _Job(N, m, k, r, d, D, rng)
            spent = 0
            while spent < PER_GROUP and time.monotonic() < deadline:
                if job.step(SLICE):
                    consider(2 * N, _edges(N, job.T, job.result))
                    return
                spent += SLICE


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 3)
    if top < d + 1:
        return best

    known = KNOWN_HALF.get((d, D), 0)
    lo_a = max(d + 1, top - 5, known + 1)
    start_b = min(lo_a - 1, known) if known else lo_a - 1

    # Phase A: try to beat the known order by searching orders just above it.
    phase_a_end = start + PHASE_A_FRAC * (deadline - start)
    if lo_a <= top:
        _phase_a(d, D, rng, lo_a, top, phase_a_end, consider)

    # Phase B: fallback descending search, only if phase A produced nothing useful.
    if start_b >= d + 1 and best[0] < 2 * start_b:
        _phase_b(d, D, rng, start_b, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
