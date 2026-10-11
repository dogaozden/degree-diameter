import itertools
import math
import random
import time

import lib

# Multi-orbit voltage lifts over semidirect groups.
#
# New helper: a regular base graph with p A-vertices and p B-vertices, where
# each A-vertex has d darts to B-vertices (A_a -- B_{(a+k) mod p}, k < d), so
# every B-vertex also receives exactly d darts. Each dart (a, b) carries a
# group voltage g, and the lift has vertices A(a,x), B(b,y) for x, y in G,
# with edges A(a,x) -- B(b, x*g). Parallel darts between the same base pair
# get distinct voltages, which keeps the lift simple and d-regular.
#
# Left multiplication by G is an automorphism of the lift, so the diameter
# test only needs BFS from the 2p orbit representatives A(a,e), B(b,e).
# The cost is the number of unreached (source, vertex) pairs, and simulated
# annealing mutates one dart voltage at a time. p = 1 recovers the bi-Cayley
# family; p = 2 and p = 3 give 4N and 6N vertex lifts.

GROUP_CAP = 4        # groups tried per order in one round
WINDOW = 6           # order candidates explored above the lower bound
PHASES = ((2, 0.55), (1, 0.20), (3, 0.25))   # (base orbits per side, time share)


# ----------------------------------------------------------------------------
# Baseline families (kept from the parent; fast and always validated).
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
# Multi-orbit lift search.
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


def _pattern(p, d):
    """Regular base darts: A_a -- B_{(a+k) mod p} for k < d. Every A and B vertex gets degree d."""
    return [(a, (a + k) % p) for a in range(p) for k in range(d)]


class _MultiOrbitLift:
    """Lift of the regular base graph over a finite group of order N, with annealable voltages."""

    def __init__(self, N, p, d, D, mul, inv):
        self.N = N
        self.p = p
        self.D = D
        self.nA = p * N
        self.V = 2 * p * N
        self.T = [[mul(x, g) for g in range(N)] for x in range(N)]
        self.invs = [inv(g) for g in range(N)]
        self.darts = _pattern(p, d)
        self.M = len(self.darts)
        # Darts sharing a base pair must carry distinct voltages (keeps the lift simple).
        self.conf = [[j for j in range(self.M)
                      if j != i and self.darts[j] == self.darts[i]]
                     for i in range(self.M)]
        # Left multiplication is an automorphism, so one source per orbit suffices.
        self.sources = [a * N for a in range(p)] + [self.nA + b * N for b in range(p)]

    def cost(self, volts):
        """Total unreached (source, vertex) pairs at distance > D over the orbit representatives."""
        N, nA, D, T, V = self.N, self.nA, self.D, self.T, self.V
        outA = [[] for _ in range(self.p)]
        outB = [[] for _ in range(self.p)]
        for i, (a, b) in enumerate(self.darts):
            g = volts[i]
            outA[a].append((b, g))
            outB[b].append((a, self.invs[g]))
        total = 0
        for s in self.sources:
            seen = bytearray(V)
            seen[s] = 1
            frontier = [s]
            cnt = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    if u < nA:
                        a, x = divmod(u, N)
                        row = T[x]
                        for b, g in outA[a]:
                            v = nA + b * N + row[g]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                    else:
                        b, y = divmod(u - nA, N)
                        row = T[y]
                        for a, gi in outB[b]:
                            v = a * N + row[gi]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                cnt += len(nxt)
                frontier = nxt
                if not frontier:
                    break
            total += V - cnt
        return total

    def _init(self, rng):
        volts = [0] * self.M
        for i in range(self.M):
            used = {volts[j] for j in self.conf[i] if j < i}
            choices = [g for g in range(self.N) if g not in used]
            volts[i] = rng.choice(choices)
        return volts

    def anneal(self, rng, deadline):
        """Anneal the dart voltages until the diameter is <= D or the deadline passes."""
        volts = self._init(rng)
        cur = self.cost(volts)
        while cur and time.monotonic() < deadline:
            i = rng.randrange(self.M)
            used = {volts[j] for j in self.conf[i]}
            g = rng.randrange(self.N)
            if g == volts[i] or g in used:
                continue
            old = volts[i]
            volts[i] = g
            v = self.cost(volts)
            if v <= cur or rng.random() < math.exp(-(v - cur) / 1.5):
                cur = v
            else:
                volts[i] = old
        return volts if cur == 0 else None

    def graph(self, volts):
        """Return (n, edges) for the lift with the given voltages."""
        N, nA = self.N, self.nA
        edges = []
        for i, (a, b) in enumerate(self.darts):
            g = volts[i]
            for x in range(N):
                edges.append((a * N + x, nA + b * N + self.T[x][g]))
        return 2 * nA, edges


def _phase(p, d, D, rng, deadline, best_n, consider):
    """Search multi-orbit lifts with p base orbits per side; ascend in order and widen the window on success."""
    Nmax = lib._moore_bound(d, D) // (2 * p)
    lo = max(d + 1, best_n // (2 * p) + 1)
    if lo > Nmax:
        return
    cands = list(range(lo, min(Nmax, lo + WINDOW - 1) + 1))
    group_cache = {}
    budget = 0.15
    while cands and time.monotonic() < deadline:
        won = None
        for N in cands:
            if time.monotonic() >= deadline:
                break
            if N not in group_cache:
                group_cache[N] = _groups(N)
            groups = group_cache[N][:]
            rng.shuffle(groups)
            for m, k, r in groups[:GROUP_CAP]:
                if time.monotonic() >= deadline:
                    break
                order, mul, inv = lib.semidirect_group(m, k, r)
                lift = _MultiOrbitLift(order, p, d, D, mul, inv)
                volts = lift.anneal(rng, min(deadline, time.monotonic() + budget))
                if volts is not None:
                    n, e = lift.graph(volts)
                    consider(n, e)
                    won = N
                    break
            if won is not None:
                break
        if won is None:
            budget *= 2
        else:
            cands = list(range(won + 1, min(Nmax, won + WINDOW) + 1))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d >= 2 and D >= 2:
        span = end - time.monotonic()
        for p, share in PHASES:
            if time.monotonic() >= end:
                break
            phase_end = min(end, time.monotonic() + share * span)
            _phase(p, d, D, rng, phase_end, best[0], consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
