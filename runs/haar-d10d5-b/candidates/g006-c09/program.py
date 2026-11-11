"""Affine-group Haar search for the bipartite degree-diameter problem (d=10, D=5).

NEW IDEA.  The parent only uses metacyclic groups.  This program adds the affine groups
Z_q x| Z_k (maps x -> a*x + b over GF(q), with a in the order-k subgroup of GF(q)^*).  Their
orders q*k fall in the window (1791, 2300], so a Haar graph over one of them has more than
3582 vertices.  Affine groups are very non-abelian, which suits the word-covering condition.

HAAR CRITERION.  For a Haar graph over G with connection set S (|S| = d), the diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The annealer minimises the number of uncovered elements
in these two sets.  The annealer moves in two ways: random replacement, and a targeted replacement
that makes an uncovered element appear as a word of the new slot.

SEARCH.  Each candidate group runs its own annealing generator.  The generators are scheduled
round-robin, so no group starves the others.  A zero-cost set is turned into a graph and checked
with lib.is_valid before it is accepted.  The parent's valid metacyclic Haar graph (3582 vertices)
is the fallback, so the output is never worse.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def _checked(graph, d, D):
    """Return graph if lib.is_valid accepts it, else the trivially valid single vertex."""
    n, e = graph
    return (n, e) if lib.is_valid(n, e, d, D) else (1, [])


def trivial(d, D):
    """Small graph for calibration cases."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def _is_prime(n):
    return n >= 2 and all(n % p for p in range(2, int(n ** 0.5) + 1))


def affine_candidates(lo, hi):
    """(order, q, k) for groups Z_q x| Z_k with q prime, k | q-1, k >= 2, and lo <= q*k <= hi, sorted by order."""
    out = []
    for q in range(3, hi + 1):
        if not _is_prime(q):
            continue
        for k in range(2, min(q, hi // q + 1)):
            if (q - 1) % k == 0 and lo <= q * k <= hi:
                out.append((q * k, q, k))
    out.sort()
    return out


def affine_group(q, k):
    """Group of maps x -> a*x + b over GF(q) with a ranging over the order-k subgroup of GF(q)^*.

    Element (a, b) is coded as pos[a]*q + b, so the identity (a=1, b=0) has code 0.
    Multiplication is (a1, b1)(a2, b2) = (a1*a2, a1*b2 + b1).  Returns (N, MT, inv).
    """
    H = [a for a in range(1, q) if pow(a, k, q) == 1]
    if len(H) != k:
        raise ValueError("k must divide q-1")
    N = k * q
    Harr = np.array(H, dtype=np.int64)
    pos = np.full(q, -1, dtype=np.int64)
    pos[Harr] = np.arange(k, dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = Harr[x // q]
    b = x % q
    MT = np.empty((N, N), dtype=np.int32)
    step = 256
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a1 = a[lo:hi, None]
        b1 = b[lo:hi, None]
        prod_a = (a1 * a[None, :]) % q
        prod_b = (a1 * b[None, :] + b1) % q
        MT[lo:hi] = pos[prod_a] * q + prod_b
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return N, MT, inv


# ------------------------------------------------------------------------------ Haar

def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, edges (g, A) ~ (s*g, B) for s in S."""
    S = np.asarray(S, dtype=np.int64)
    ar = np.arange(N, dtype=np.int64)
    src = np.tile(ar, len(S))
    dst = N + MT[S].astype(np.int64).ravel()
    return 2 * N, list(zip(src.tolist(), dst.tolist()))


def word_cover(MT, inv, S, N):
    """Boolean coverage arrays for (S^-1 S)^2 and (S S^-1)^2."""
    iS = inv[S]
    P1 = MT[iS[:, None], S[None, :]].ravel()
    P2 = MT[S[:, None], iS[None, :]].ravel()
    cov1 = np.zeros(N, dtype=bool)
    cov1[MT[P1[:, None], P1[None, :]].ravel()] = True
    cov2 = np.zeros(N, dtype=bool)
    cov2[MT[P2[:, None], P2[None, :]].ravel()] = True
    return cov1, cov2


def anneal_gen(N, MT, inv, d, rng, L=4000):
    """Generator: one annealing step per yield.  Yields ('found', S) at zero cost, then ends."""
    while True:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cov1, cov2 = word_cover(MT, inv, S, N)
        cur = 2 * N - int(cov1.sum()) - int(cov2.sum())
        if cur == 0:
            yield ('found', S.copy())
            return
        for step in range(L):
            k = int(rng.integers(d))
            if rng.random() < 0.4:
                # Targeted move: make an uncovered word appear through slot k.
                use1 = rng.random() < 0.5
                cov = cov1 if use1 else cov2
                unc = np.flatnonzero(~cov)
                if len(unc) == 0:
                    yield None
                    continue
                u = int(unc[int(rng.integers(len(unc)))])
                j = int(rng.integers(d - 1))
                if j >= k:
                    j += 1
                if use1:
                    g = int(MT[S[j], u])
                else:
                    g = int(MT[int(inv[u]), S[j]])
            else:
                g = int(rng.integers(N))
            if np.any(S == g):
                yield None
                continue
            old = int(S[k])
            S[k] = g
            n1, n2 = word_cover(MT, inv, S, N)
            c = 2 * N - int(n1.sum()) - int(n2.sum())
            temp = 0.5 + 1.5 * (1.0 - step / L)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
                cov1, cov2 = n1, n2
                if cur == 0:
                    yield ('found', S.copy())
                    return
            else:
                S[k] = old
            yield None


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _checked(trivial(d, D), d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT0, _ = group_table(m, k, r)
        n, e = haar_edges(MT0, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    tasks = []
    for N, q, kk in affine_candidates(best_n // 2 + 1, 2300)[:7]:
        try:
            N2, MT, inv = affine_group(q, kk)
        except Exception:
            continue
        tasks.append({'N': N2, 'MT': MT, 'inv': inv,
                      'gen': anneal_gen(N2, MT, inv, d, rng)})

    while tasks and time.monotonic() < deadline:
        for task in list(tasks):
            if time.monotonic() >= deadline:
                break
            if 2 * task['N'] <= best_n:
                tasks.remove(task)
                continue
            try:
                out = next(task['gen'])
            except Exception:
                tasks.remove(task)
                continue
            if out is None:
                continue
            # Zero-cost set found; this task's generator is finished.
            tasks.remove(task)
            try:
                n, e = haar_edges(task['MT'], out[1], task['N'])
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_edges = n, e
            except Exception:
                pass

    if best_edges is None:
        return _checked(trivial(d, D), d, D)
    return best_n, best_edges
