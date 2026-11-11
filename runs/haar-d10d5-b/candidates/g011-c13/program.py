"""Bold variant for the d=10, D=5 target: Haar graphs over metacyclic groups of order 2001..2100
(so 2|G| > 4000 beats the record), searched with automorphism-orbit-invariant sets.

Idea: for a multiplier automorphism phi of G, restrict S to a union of phi-orbits. Moves swap whole
orbits of equal size, so the search space is much smaller and the cost structure is preserved.
The identity automorphism is included, giving the plain element-swap search as one option.

Every returned graph is checked with lib.is_valid. If nothing reaches cost 0, a valid smaller Haar
graph (FALLBACK) is returned, and a trivially valid graph for any other case.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
SLICE = 2.5                 # seconds per (group, automorphism) attempt
N_LO, N_HI = 2001, 2100     # group orders; 2|G| must exceed the record 4000


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> index a*k + j, (a, j)(b, l) = (a + lam^j b, j + l)."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("need lam^k = 1 mod m")
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


def metacyclic_candidates(lo, hi, cap, rng):
    """Random sample of (m, k, lam) with m*k in [lo, hi], lam != 1, lam^k = 1 mod m, gcd(lam, m) = 1."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, min(N // 2, 40) + 1):
            if N % k:
                continue
            m = N // k
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
    order = rng.permutation(len(out))[:cap]
    return [out[int(i)] for i in order]


def automorphisms(MT, m, k, rng, count=3):
    """Identity plus up to count-1 multiplier automorphisms (a, j) -> (u a, j) of small order, verified."""
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    found = [np.arange(N, dtype=np.int64)]
    units = [u for u in range(2, m) if math.gcd(u, m) == 1]
    for idx in rng.permutation(len(units)):
        if len(found) >= count:
            break
        u = units[int(idx)]
        x, o = u, 1
        while x != 1 and o <= 6:
            x = (x * u) % m
            o += 1
        if x != 1 or o < 2 or o > 6:
            continue
        perm = ((u * a) % m) * k + j
        # phi is an automorphism iff MT[phi x, phi y] = phi(MT[x, y]) for all x, y.
        if np.array_equal(MT[perm[:, None], perm[None, :]], perm[MT]):
            found.append(perm)
    return found


# ----------------------------------------------------------------------------- cost

def cost(MT, inv, S):
    """Uncovered group elements over both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    total = 0
    for P in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
        P = np.unique(P)
        cov = np.zeros(N, dtype=bool)
        cov[MT[P[:, None], P[None, :]].ravel()] = True
        total += N - int(cov.sum())
    return total


def orbits_of(perm):
    """Cycles of the permutation perm, as int32 arrays."""
    N = len(perm)
    seen = np.zeros(N, dtype=bool)
    out = []
    for x in range(N):
        if seen[x]:
            continue
        orb = [x]
        seen[x] = True
        y = int(perm[x])
        while y != x:
            orb.append(y)
            seen[y] = True
            y = int(perm[y])
        out.append(np.array(orb, dtype=np.int32))
    return out


# ----------------------------------------------------------------------------- search

def init_sel(sizes, d, rng):
    """Random set of orbit indices whose sizes sum to exactly d, or None."""
    for _ in range(300):
        order = rng.permutation(len(sizes))
        sel, tot = [], 0
        for idx in order:
            s = sizes[int(idx)]
            if tot + s <= d:
                sel.append(int(idx))
                tot += s
                if tot == d:
                    return set(sel)
    return None


def orbit_anneal(MT, inv, d, orbits, deadline, rng, temp=0.6, patience=2500):
    """Anneal over unions of orbits of total size d; moves swap a chosen orbit for an unchosen one of equal size."""
    sizes = [len(o) for o in orbits]
    bysize = {}
    for i, s in enumerate(sizes):
        bysize.setdefault(s, []).append(i)

    def build(sel):
        return np.concatenate([orbits[i] for i in sel]).astype(np.int32)

    sel = init_sel(sizes, d, rng)
    if sel is None:
        return None, 10 ** 9
    S = build(sel)
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    since = 0
    while bestc > 0 and time.monotonic() < deadline:
        if since > patience:
            sel = init_sel(sizes, d, rng)
            if sel is None:
                break
            S = build(sel)
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            continue
        slist = list(sel)
        a = slist[int(rng.integers(len(slist)))]
        pool = bysize[sizes[a]]
        b = None
        for _ in range(8):
            cand = pool[int(rng.integers(len(pool)))]
            if cand not in sel:
                b = cand
                break
        since += 1
        if b is None:
            continue
        new_sel = (sel - {a}) | {b}
        NS = build(new_sel)
        c = cost(MT, inv, NS)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            sel, S, cur = new_sel, NS, c
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
    return best, bestc


# ----------------------------------------------------------------------------- graph

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S if lib.is_valid accepts it, else None."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other case."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    cands = metacyclic_candidates(N_LO, N_HI, 60, rng)
    for ci in range(len(cands)):
        if time.monotonic() > deadline - SLICE:
            break
        m, k, lam = cands[ci]
        try:
            MT, inv = group_meta(m, k, lam)
            autos = automorphisms(MT, m, k, rng)
        except Exception:
            continue
        for perm in autos:
            now = time.monotonic()
            if now >= deadline - 1.0:
                break
            end = min(deadline - 1.0, now + SLICE)
            try:
                S, c = orbit_anneal(MT, inv, d, orbits_of(perm), end, rng)
            except Exception:
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        g = run(d, D, seed, time_limit)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
