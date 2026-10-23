"""Bold variant: multi-base voltage lifts over non-abelian groups, with the parent's Haar search kept as a safe arm.

NEW IDEA.  A bipartite base multigraph with p A-vertices and p B-vertices, each vertex of degree 6 (a sum of 6 random
permutation matrices), lifted over a non-abelian group G of order N.  The lift has 2pN vertices and is 6-regular.
Left multiplication by h maps (u, x) to (u, hx) and is an automorphism of the lift, so every fibre is one orbit.
Hence diameter <= 5 iff every base vertex's root (u, e) reaches the whole lift within 5 steps.  The cost is the total
number of unreached vertices over the 2p roots, which needs only 2p small BFS runs per evaluation.

Orders are chosen so 2pN > 684, which would beat the record.  p = 2, 3, 4 give smaller groups than the Haar search needs.

SAFETY.  The lift arm runs first.  The parent's Haar search runs on the remaining time.  Each result is checked with
lib.is_valid, and the larger valid graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5
TARGET_N = 684


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^*."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def metacyclic_candidates(lo, hi, per_pair, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if lam % m != 1 and math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    cnt += 1
                    if cnt >= per_pair:
                        break
            if len(out) >= limit:
                return out
    return out


# ============================================================================ lift arm (new)

class Lift:
    """A 2p-vertex base multigraph (p A, p B, 6-regular) with a voltage in G on each dart."""

    def __init__(self, p, N, MT, rng):
        self.p, self.N, self.MT = p, N, MT
        M = np.zeros((p, p), dtype=np.int64)
        for _ in range(DEG):
            M[np.arange(p), rng.permutation(p)] += 1
        pu, pv = [], []
        for i in range(p):
            for j in range(p):
                for _ in range(int(M[i, j])):
                    pu.append(i)
                    pv.append(j)
        self.pu = np.array(pu, dtype=np.int64)
        self.pv = np.array(pv, dtype=np.int64)
        self.T = len(pu)
        self.g = np.zeros(self.T, dtype=np.int64)
        for i in range(p):
            for j in range(p):
                idx = np.nonzero((self.pu == i) & (self.pv == j))[0]
                if len(idx):
                    # Parallel darts need distinct voltages, or the lift would lose edges.
                    self.g[idx] = rng.choice(N, size=len(idx), replace=False)
        self.x = np.arange(N, dtype=np.int64)

    def nbr(self, g):
        """Neighbour table (2pN, DEG). A-vertex u*N+x and B-vertex (p+v)*N+y; dart (u,v,g) joins (u,x) to (v,x*g)."""
        N, p = self.N, self.p
        srcs, dsts = [], []
        for s in range(self.T):
            a = self.pu[s] * N + self.x
            b = (p + self.pv[s]) * N + self.MT[self.x, g[s]]
            srcs += [a, b]
            dsts += [b, a]
        src = np.concatenate(srcs)
        dst = np.concatenate(dsts)
        order = np.argsort(src, kind="stable")
        return dst[order].reshape(2 * p * N, DEG)

    def cost(self, nb):
        """Total unreached vertices over the 2p roots (u, identity), within DIAM steps. Zero iff diameter <= DIAM."""
        n = nb.shape[0]
        total = 0
        for r in range(2 * self.p):
            seen = np.zeros(n, dtype=bool)
            root = r * self.N
            seen[root] = True
            frontier = np.array([root], dtype=np.int64)
            for _ in range(DIAM):
                nxt = nb[frontier].ravel()
                nxt = nxt[~seen[nxt]]
                if nxt.size == 0:
                    break
                frontier = np.unique(nxt)
                seen[frontier] = True
            total += n - int(seen.sum())
        return total

    def edges(self, nb):
        n_a = self.p * self.N
        return 2 * n_a, [(a, int(b)) for a in range(n_a) for b in nb[a]]

    def propose(self, rng):
        """Pick a dart and a new voltage not already used by a parallel dart in the same pair."""
        s = int(rng.integers(self.T))
        same = (self.pu == self.pu[s]) & (self.pv == self.pv[s])
        used = set(int(v) for v in self.g[same])
        while True:
            c = int(rng.integers(self.N))
            if c not in used:
                return s, c


class Runner:
    """Metropolis search over voltages for one (p, group), with restarts when stuck."""

    def __init__(self, p, N, MT, rng):
        self.p, self.N, self.MT, self.rng = p, N, MT, rng
        self.new_state()

    def new_state(self):
        self.st = Lift(self.p, self.N, self.MT, self.rng)
        self.nb = self.st.nbr(self.st.g)
        self.cur = self.st.cost(self.nb)
        self.since = 0

    def run(self, t_end, temp=2.0, patience=3000):
        """Return (n, edges) as soon as the cost hits zero, else None at t_end."""
        while time.monotonic() < t_end:
            if self.cur == 0:
                return self.st.edges(self.nb)
            if self.since > patience:
                self.new_state()
                continue
            s, c = self.st.propose(self.rng)
            old = int(self.st.g[s])
            self.st.g[s] = c
            nb = self.st.nbr(self.st.g)
            new = self.st.cost(nb)
            delta = new - self.cur
            if delta <= 0 or self.rng.random() < math.exp(-delta / temp):
                self.cur = new
                self.nb = nb
                self.since = 0 if delta < 0 else self.since + 1
            else:
                self.st.g[s] = old
                self.since += 1
        return None


def lift_arm(t_end, rng, best_n):
    """Round-robin over (p, group) candidates whose order exceeds best_n; return the largest valid lift found."""
    cands = []
    for p in (2, 3, 4):
        Nmin = -(-(best_n + 1) // (2 * p))  # smallest N with 2pN > best_n
        for N, m, k, lam in metacyclic_candidates(Nmin, Nmin + 6, 2, 6):
            cands.append((p, N, m, k, lam))
    cands = cands[:12]
    runners = [None] * len(cands)
    best = None
    slice_len = 0.6
    while time.monotonic() < t_end - 0.2:
        active = [i for i, (p, N, _, _, _) in enumerate(cands) if 2 * p * N > best_n]
        if not active:
            break
        for idx in active:
            p, N, m, k, lam = cands[idx]
            now = time.monotonic()
            if now >= t_end:
                break
            if 2 * p * N <= best_n:
                continue
            if runners[idx] is None:
                MT, _ = group_meta(m, k, lam)
                runners[idx] = Runner(p, N, MT, rng)
            found = runners[idx].run(min(t_end, now + slice_len))
            if found is not None:
                n, edges = found
                if n > best_n and lib.is_valid(n, edges, DEG, DIAM):
                    best_n, best = n, (n, edges)
                else:
                    runners[idx].new_state()
        slice_len = min(slice_len * 1.5, 5.0)
    return best


# ============================================================================ Haar arm (parent search)

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]].ravel())
    P1 = np.unique(MT[S[:, None], Si[None, :]].ravel())
    return (N - int(_cover(MT, N, P0).sum())) + (N - int(_cover(MT, N, P1).sum()))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
        if side == 0:
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group, with restarts. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
            cur = None
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S, cur = None, None
    return best, bestc


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """Time-sliced round-robin over the plan; returns a valid graph (fallback or trivial if nothing succeeds)."""
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    cache = {}
    slice_len = 0.5
    while time.monotonic() < deadline - 0.05:
        for idx, (name, builder) in enumerate(plan):
            now = time.monotonic()
            if now >= deadline:
                break
            if idx not in cache:
                try:
                    cache[idx] = builder()
                except Exception:
                    cache[idx] = None
            if cache[idx] is None:
                continue
            MT, inv = cache[idx]
            end = min(deadline, now + slice_len)
            try:
                S, c = search(MT, inv, d, end, rng)
            except Exception:
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
        slice_len = min(slice_len * 1.5, 6.0)
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13)),
    ('Heis(7), order 343', lambda: group_heis(7)),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5)),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18)),
]
for _N, _m, _k, _lam in metacyclic_candidates(343, 372, 2, 28):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))
for _N, _m, _k, _lam in metacyclic_candidates(342, 342, 2, 4):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


# ============================================================================ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    candidates = []
    try:
        rng = np.random.default_rng(seed)
        lift = lift_arm(t0 + 0.35 * time_limit, rng, TARGET_N)
        if lift is not None:
            candidates.append(lift)
    except Exception:
        pass
    rem = t0 + 0.85 * time_limit - time.monotonic()
    if rem > 1.0:
        try:
            g = run(d, D, seed, rem / 0.8, PLAN, FALLBACK)
            candidates.append(g)
        except Exception:
            pass
    best = None
    for n, edges in sorted(candidates, key=lambda c: -c[0]):
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            break
    if best is None:
        return trivial(d, D)
    return best
