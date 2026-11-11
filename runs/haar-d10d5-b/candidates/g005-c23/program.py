"""Haar-graph search for the d=10, D=5 target, using targeted coverage moves.

HAAR CRITERION. For a finite group G and a connection set S of d distinct elements, the Haar graph has vertices
A_g, B_g (g in G) and edges A_g ~ B_{s g} (s in S). It is bipartite and d-regular with 2|G| vertices. Its diameter
is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G. The cost is the number of uncovered elements of the two sets.

NEW IDEA (not used by the parent): TARGETED SOLVE MOVES. Pick an uncovered element u of one covering set, and a
4-letter word pattern (signs -,+,-,+ for the S^-1 S side; +,-,+,- for the S S^-1 side). Choose a slot k of the word
and let the slot hold the element being replaced. The other three letters come from the rest of S. Solving the word
equation for that slot gives a replacement x for which the word equals u exactly. Such a move always covers u.
The other proposals are random replacements. All proposals use Metropolis acceptance on the full cost.

SEARCH. Several annealing tasks run round-robin over metacyclic groups Z_m x| Z_k of orders just above the best
known half-order. A zero-cost set is built into a Haar graph and checked with lib.is_valid before acceptance.
The validated fallback is the parent's Z_199 x| Z_9 Haar graph (3582 vertices).
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)

FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

POOL = 6
BATCH = 20
STUCK_LIMIT = 2500
P_TARGETED = 0.7
SPAN = 80


# ------------------------------------------------------------------ small fallbacks

def safe_small(d, D):
    """A small graph that is valid for any (d, D), verified with lib.is_valid when possible."""
    cands = []
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            cands.append(lib.projective_plane_incidence(d - 1))
    except Exception:
        pass
    if d >= 1 and D >= 2:
        cands.append(lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2
    if d >= 1 and D >= 1:
        cands.append(lib.haar_graph(1, [0]))       # K_2
    cands.append((1, []))
    for n, e in cands:
        try:
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 1, []


# ------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k, element (a, j) coded as a*k + j, with (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv): MT[g, h] = g*h, inv[g] = g^-1. The identity is code 0.
    """
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 256
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def metacyclic_options(N):
    """All (m, k, [r...]) with m*k = N, k >= 2, and r a nontrivial action with r^k = 1 mod m."""
    opts = []
    for m in range(3, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if rs:
            opts.append((m, k, rs))
    return opts


def random_group(N, rng):
    """A random non-abelian metacyclic group of order N, or the cyclic group if none exists."""
    opts = metacyclic_options(N)
    if not opts:
        return group_table(1, N, 1)
    m, k, rs = opts[int(rng.integers(len(opts)))]
    r = rs[int(rng.integers(len(rs)))]
    return group_table(m, k, r)


# ------------------------------------------------------------------ cost

def cover_masks(MT, inv, S, N):
    """Return (cost, ma, mb): ma marks (S^-1 S)^2, mb marks (S S^-1)^2, cost counts uncovered elements."""
    Si = inv[S]
    P = MT[Si[:, None], S[None, :]].ravel()
    PP = MT[P[:, None], P[None, :]].ravel()
    ma = np.zeros(N, dtype=bool)
    ma[PP] = True
    Q = MT[S[:, None], Si[None, :]].ravel()
    QQ = MT[Q[:, None], Q[None, :]].ravel()
    mb = np.zeros(N, dtype=bool)
    mb[QQ] = True
    cost = 2 * N - int(ma.sum()) - int(mb.sum())
    return cost, ma, mb


# ------------------------------------------------------------------ moves

def targeted_move(MT, inv, S, N, d, ma, mb, rng):
    """Solve a word equation for one slot so that a chosen uncovered element becomes covered.

    Word for side 0 is s1^-1 s2 s3^-1 s4; side 1 is s1 s2^-1 s3 s4^-1. The slot k of the word is the element
    being replaced, and the other three letters come from S minus that slot. Returns the new S, or None.
    """
    avail = []
    if not ma.all():
        avail.append(0)
    if not mb.all():
        avail.append(1)
    if not avail:
        return None
    side = avail[int(rng.integers(len(avail)))]
    unc = np.flatnonzero(~ma) if side == 0 else np.flatnonzero(~mb)
    u = int(unc[int(rng.integers(len(unc)))])
    signs = (-1, 1, -1, 1) if side == 0 else (1, -1, 1, -1)
    k = int(rng.integers(4))
    slot = int(rng.integers(d))
    others = [i for i in range(d) if i != slot]
    idx = [others[int(rng.integers(len(others)))] for _ in range(4)]
    idx[k] = slot
    letters = [None] * 4
    for j in range(4):
        if j == k:
            continue
        g = int(S[idx[j]])
        letters[j] = g if signs[j] == 1 else int(inv[g])
    L = 0
    for j in range(k):
        L = int(MT[L, letters[j]])
    R = 0
    for j in range(3, k, -1):
        R = int(MT[letters[j], R])
    if signs[k] == 1:
        # word = L x R = u  ->  x = L^-1 u R^-1
        x = int(MT[MT[int(inv[L]), u], int(inv[R])])
    else:
        # word = L x^-1 R = u  ->  x = R u^-1 L
        x = int(MT[MT[R, int(inv[u])], L])
    if x in set(S.tolist()):
        return None
    S2 = S.copy()
    S2[slot] = x
    return S2


def random_move(S, N, d, rng):
    Sset = set(S.tolist())
    while True:
        x = int(rng.integers(N))
        if x not in Sset:
            break
    S2 = S.copy()
    S2[int(rng.integers(d))] = x
    return S2


class Task:
    """One annealing run over connection sets in a fixed group."""

    def __init__(self, N, MT, inv, d, rng):
        self.N, self.MT, self.inv, self.d, self.rng = N, MT, inv, d, rng
        self.S = rng.choice(N, d, replace=False).astype(np.int64)
        self.cur, self.ma, self.mb = cover_masks(MT, inv, self.S, N)
        self.best = self.cur
        self.since = 0
        self.T = float(rng.uniform(0.3, 1.0))

    def step(self):
        """One proposal. Returns True when the cost reaches zero."""
        cand = None
        if self.rng.random() < P_TARGETED:
            cand = targeted_move(self.MT, self.inv, self.S, self.N, self.d,
                                 self.ma, self.mb, self.rng)
        if cand is None:
            cand = random_move(self.S, self.N, self.d, self.rng)
        c, ma, mb = cover_masks(self.MT, self.inv, cand, self.N)
        if c <= self.cur or self.rng.random() < math.exp(-(c - self.cur) / self.T):
            self.S, self.cur, self.ma, self.mb = cand, c, ma, mb
            if self.cur == 0:
                return True
        if self.cur < self.best:
            self.best = self.cur
            self.since = 0
        else:
            self.since += 1
        return False

    def stuck(self):
        return self.since > STUCK_LIMIT


# ------------------------------------------------------------------ output

def haar_from(MT, S, N):
    """Haar graph: vertices A_g = g and B_g = N + g; edges A_g ~ B_{s g} for s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted({int(x) for x in S}):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    def spawn():
        lo = best_n // 2 + 1
        N = lo + int(rng.integers(SPAN))
        MT, inv = random_group(N, rng)
        return Task(N, MT, inv, d, rng)

    pool = []
    for _ in range(POOL):
        if time.monotonic() >= deadline:
            break
        pool.append(spawn())

    while pool and time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if 2 * task.N <= best_n or task.stuck():
                pool[idx] = spawn()
                continue
            found = False
            for _ in range(BATCH):
                if task.step():
                    found = True
                    break
            if found:
                try:
                    n, edges = haar_from(task.MT, task.S, task.N)
                    if n > best_n and lib.is_valid(n, edges, d, D):
                        best_n, best_edges = n, edges
                except Exception:
                    pass
                pool[idx] = spawn()

    if best_edges is None:
        return safe_small(d, D)
    return best_n, best_edges
