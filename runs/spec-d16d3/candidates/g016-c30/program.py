import math
import random
import time

import lib

_ITERS = 6000


# ----------------------------------------------------------------------------
# Safe fallback: K_{d,d} (diameter 2), or K_2 / a single vertex for tiny cases.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


# ----------------------------------------------------------------------------
# Baseline: PG(2, q) incidence plus an arc-extension (diameter 3).
# Largest prime power q with q + 1 <= d; spare degree s = d - q - 1 is used by
# adding an A-vertex per point of S and a B-vertex per line of S.
# ----------------------------------------------------------------------------

def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _ok_add(P, cl, cp, s, pl, lp):
    for L in pl[P]:
        if cl[L] >= s:
            return False
    for Q in lp[P]:
        if cp[Q] >= s:
            return False
    return True


def _arc_graph(m, edges, pl, lp, S):
    n0 = 2 * m
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = n0 + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, P in enumerate(S):
        b = n0 + k + t
        for Q in lp[P]:
            E.append((Q, b))
    return n0 + 2 * k, E


def _arc_baseline(d, deadline, rng):
    q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
    if q is None:
        return None
    s = d - q - 1
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    if s <= 0:
        return n2, edges
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)

    best_S = []
    if s >= 2:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(best_S):
            best_S = cs

    order = list(range(m))
    gbest = []
    trials = 0
    while trials < 300 and time.monotonic() < deadline:
        trials += 1
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if _ok_add(P, cl, cp, s, pl, lp):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(gbest):
            gbest = S
    if len(gbest) > len(best_S):
        best_S = gbest

    if not best_S:
        return n2, edges
    return _arc_graph(m, edges, pl, lp, best_S)


# ----------------------------------------------------------------------------
# Bold new family: bi-Cayley graphs over small groups (diameter 3).
#
# Let G be a group and S a set of d elements. Join (x,0) to (s x,1) for s in S.
# Same-side distances are <= 2 iff S^{-1}S = G (side 0) and S S^{-1} = G (side 1),
# and cross-side distances are <= 3 under the same conditions. So we search for
# a d-subset S covering G twice over, maximising |G|. Each side has |G| vertices,
# so the order is 2|G|. The Moore bound is |G| <= d(d-1)+1, which is 241 for d=16.
# Perfect difference sets need d-1 to be a prime power, so for d=16 we search for
# near-perfect covers by simulated annealing with incremental coverage counts.
# ----------------------------------------------------------------------------

class _Cover:
    """Coverage counts for the tables L[s][t] = s^-1 t and R[s][t] = s t^-1 over the set S."""

    def __init__(self, N, tabs, S):
        self.N = N
        self.tabs = tabs
        self.S = list(S)
        self.inS = [False] * N
        for s in self.S:
            self.inS[s] = True
        self.cnt = []
        z = 0
        for T in tabs:
            c = [0] * N
            for s in self.S:
                row = T[s]
                for t in self.S:
                    c[row[t]] += 1
            self.cnt.append(c)
            z += sum(1 for x in c if x == 0)
        self.zeros = z

    def replace(self, i, b):
        """Replace S[i] by b (b not in S); return the number of uncovered (table, element) cells."""
        a = self.S[i]
        others = [t for j, t in enumerate(self.S) if j != i]
        z = self.zeros
        for T, c in zip(self.tabs, self.cnt):
            ra = T[a]
            for t in others:
                x = ra[t]
                c[x] -= 1
                if c[x] == 0:
                    z += 1
                x = T[t][a]
                c[x] -= 1
                if c[x] == 0:
                    z += 1
            x = ra[a]
            c[x] -= 1
            if c[x] == 0:
                z += 1
            rb = T[b]
            for t in others:
                x = rb[t]
                if c[x] == 0:
                    z -= 1
                c[x] += 1
                x = T[t][b]
                if c[x] == 0:
                    z -= 1
                c[x] += 1
            x = rb[b]
            if c[x] == 0:
                z -= 1
            c[x] += 1
        self.S[i] = b
        self.inS[a] = False
        self.inS[b] = True
        self.zeros = z
        return z


def _tables(m, k, r):
    """Return (N, tabs, mul) for Z_m x| Z_k (cyclic when k == 1)."""
    if k == 1:
        N = m
        L = [[(t - s) % N for t in range(N)] for s in range(N)]
        R = [[(s - t) % N for t in range(N)] for s in range(N)]

        def mul(s, g):
            return (s + g) % N

        return N, [L, R], mul
    N, mul, inv = lib.semidirect_group(m, k, r)
    iv = [inv(x) for x in range(N)]
    L = [[mul(iv[s], t) for t in range(N)] for s in range(N)]
    R = [[mul(s, iv[t]) for t in range(N)] for s in range(N)]
    return N, [L, R], mul


def _random_group(N, rng):
    if rng.random() < 0.5:
        return N, 1, 1
    divs = [k for k in range(2, N // 2 + 1) if N % k == 0]
    if not divs:
        return N, 1, 1
    k = rng.choice(divs)
    m = N // k
    if m < 2:
        return N, 1, 1
    for _ in range(80):
        r = rng.randrange(1, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return m, k, r
    return N, 1, 1


def _attempt(N, tabs, d, rng, iters, deadline):
    """Anneal a d-set S containing the identity (index 0) with full coverage in both tables."""
    S = [0] + rng.sample(range(1, N), d - 1)
    st = _Cover(N, tabs, S)
    cur = st.zeros
    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break
        T = 0.5 * (1.0 - it / iters) + 0.05
        i = rng.randrange(1, d)
        b = rng.randrange(N)
        if st.inS[b]:
            continue
        a = st.S[i]
        new = st.replace(i, b)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            st.replace(i, a)
    return list(st.S) if cur == 0 else None


def _group_edges(N, S, mul):
    E = [(g, N + mul(s, g)) for s in S for g in range(N)]
    return 2 * N, E


def _group_search(d, D, best, deadline, rng):
    hi = d * (d - 1) + 1
    lo = best[0] // 2 + 1
    while lo <= hi and time.monotonic() < deadline:
        success = False
        for N in range(lo, hi + 1):
            if time.monotonic() >= deadline:
                break
            if N < d:
                continue
            m, k, r = _random_group(N, rng)
            N2, tabs, mul = _tables(m, k, r)
            S = _attempt(N2, tabs, d, rng, _ITERS, deadline)
            if S is not None:
                n, edges = _group_edges(N2, S, mul)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                lo = N + 1
                success = True
                break
        if not success and time.monotonic() >= deadline:
            break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    best = _fallback(d, D)
    if D < 3 or d < 2:
        return best

    try:
        cand = _arc_baseline(d, start + 0.15 * (deadline - start), rng)
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    try:
        best = _group_search(d, D, best, deadline, rng)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
