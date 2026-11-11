"""Bold variant for d=6, D=5: Haar graphs over non-abelian metacyclic groups.

CONSTRUCTION.  Take a group G of order M and a 6-element set S.  The Haar graph has A-vertices g and
B-vertices N+g (N = M), with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, 6-regular, and has 2M vertices.
Right multiplication by h is an automorphism, so each side is vertex-transitive.  Therefore the diameter is at
most 5 iff the two sources (e, A) and (e, B) each reach all 2M vertices within 5 steps.  The search anneals S
with that exact uncovered-count cost, using a numpy BFS.

GROUPS.  Non-abelian metacyclic groups Z_a x|_lam Z_k with a*k = M, lam != 1, for orders M >= 331.  Order 342 gives
684 vertices (the record), and larger orders give more.

SAFETY.  Every candidate is rebuilt explicitly and checked with lib.is_valid.  The checked Haar graph of order 660
is the fallback, and a 12-vertex K_{6,6} is used if that fails.
"""
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = (((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k
                     + (j[lo:hi, None] + j[None, :]) % k)
    return _finish(MT)


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


TARGET = (6, 5)
FALLBACK_S = [0, 179, 116, 180, 47, 306]   # valid Haar graph of order 330 in group_meta(33, 10, 26)


def fallback_graph(d, D):
    """Checked Haar graph of order 660; trivial graph if anything goes wrong."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------ Haar-graph search

SLICE = 1.5        # seconds per (group, attempt)
STALL_LIMIT = 2000
TEMP = 0.6


def group_queue(lo_orders, rnd):
    """Non-abelian metacyclic (a, k, lam) with a*k = M, grouped by order M, in the order given."""
    queue = []
    for M in lo_orders:
        grp = []
        for k in range(1, M + 1):
            if M % k:
                continue
            a = M // k
            if a < 2:
                continue
            for lam in range(2, a):
                if math.gcd(lam, a) == 1 and pow(lam, k, a) == 1 % a:
                    grp.append((a, k, lam))
        rnd.shuffle(grp)
        queue += grp
    return queue


def set_slot(nb, MT, INV, N, i, s):
    """Store the two neighbour columns contributed by connection element s in slot i."""
    nb[:N, i] = N + MT[s]          # A-vertex g  -> B-vertex s*g
    nb[N:, i] = MT[INV[s]]         # B-vertex h  -> A-vertex s^-1 * h


def coverage_cost(nb, N):
    """Uncovered vertices from the two sources (e, A) and (e, B) within 5 steps.  Zero means diameter <= 5."""
    total_v = 2 * N
    tot = 0
    for src in (0, N):
        vis = np.zeros(total_v, dtype=bool)
        vis[src] = True
        fr = vis.copy()
        for _ in range(5):
            idx = np.flatnonzero(fr)
            nxt = np.zeros(total_v, dtype=bool)
            nxt[nb[idx].ravel()] = True
            nxt &= ~vis
            if not nxt.any():
                break
            vis |= nxt
            fr = nxt
        tot += total_v - int(vis.sum())
    return tot


def anneal(MT, INV, N, d, dl, rng):
    """Anneal a d-subset S of G.  Returns S (a list) with cost 0, or None at the deadline."""
    S = [int(x) for x in rng.choice(N, size=d, replace=False)]
    nb = np.empty((2 * N, d), dtype=np.int64)
    for i, s in enumerate(S):
        set_slot(nb, MT, INV, N, i, s)
    cur = coverage_cost(nb, N)
    stall = 0
    while True:
        if cur == 0:
            return S
        if time.monotonic() >= dl:
            return None
        i = int(rng.integers(d))
        new_s = int(rng.integers(N))
        if new_s in S:
            continue
        old_s = S[i]
        set_slot(nb, MT, INV, N, i, new_s)
        c = coverage_cost(nb, N)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            S[i] = new_s
            stall = 0 if c < cur else stall + 1
            cur = c
        else:
            set_slot(nb, MT, INV, N, i, old_s)
            stall += 1
        if stall > STALL_LIMIT:
            S = [int(x) for x in rng.choice(N, size=d, replace=False)]
            for j, s in enumerate(S):
                set_slot(nb, MT, INV, N, j, s)
            cur = coverage_cost(nb, N)
            stall = 0


# ------------------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)
    rnd = random.Random(seed)

    best = fallback_graph(d, D)
    best_n = best[0]

    # Order priority: 342 (matches record 684), then 343+ (beats it), then 331..341.
    orders = [342] + list(range(343, 401)) + list(range(331, 342))
    queue = group_queue(orders, rnd)
    if not queue:
        return best

    qi = 0
    while time.monotonic() < end:
        a, k, lam = queue[qi % len(queue)]
        qi += 1
        N = a * k
        if 2 * N <= best_n:
            continue
        dl = min(end, time.monotonic() + SLICE)
        try:
            MT, INV = group_meta(a, k, lam)
            S = anneal(MT, INV, N, d, dl, rng)
        except Exception:
            continue
        if S is None:
            continue
        try:
            n, edges = haar_edges(MT, S)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
        except Exception:
            pass
    return best
