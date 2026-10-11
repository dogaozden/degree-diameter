import math
import random
import time
from math import gcd

import lib

TIME_FRAC = 0.8     # fraction of time_limit used before returning
MARGIN = 3.0        # seconds kept in reserve
STEPS = 4000        # annealing steps per restart
T0 = 1.5            # starting temperature
T1 = 0.1            # final temperature
MAX_GROUPS = 6      # groups tried per order


# ---------------------------------------------------------------- fallbacks

def _fallback(d, D):
    """Best verified known construction (no search). Returns (n, edges) or None."""
    cands = []
    try:
        if D == 3 and lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))
    except Exception:
        pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    try:
        cands.append(lib.haar_graph(d, range(d)))   # K_{d,d}, diameter 2
    except Exception:
        pass
    best = None
    for n, e in cands:
        try:
            if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
                best = (n, e)
        except Exception:
            pass
    return best


# ---------------------------------------------------------------- groups

def _tables(order, mul_f, inv_f):
    mul = [[mul_f(x, y) for y in range(order)] for x in range(order)]
    inv = [inv_f(x) for x in range(order)]
    return mul, inv


def _groups(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k with m*k = N."""
    out = []
    o, mf, ivf = lib.cyclic_group(N)
    out.append(_tables(o, mf, ivf))
    cands = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            cands.append((m, k, r))
    rng.shuffle(cands)
    for m, k, r in cands[:MAX_GROUPS - 1]:
        try:
            o, mf, ivf = lib.semidirect_group(m, k, r)
            out.append(_tables(o, mf, ivf))
        except Exception:
            pass
    return out


# ---------------------------------------------------------------- search

# Bi-Cayley graph over group G with connection set S (|S| = d):
#   a_x ~ b_{x*s} for s in S.  Vertices a_x = x, b_y = N + y.
# Left translation is an automorphism, so diameter <= 3 holds iff
#   S S^{-1} = G  and  S^{-1} S = G.
# Cost = number of uncovered group elements (0 means valid).

def _cost(S, N, mul, inv):
    invS = [inv[s] for s in S]
    A = set()
    B = set()
    for s in S:
        row = mul[s]
        for ti in invS:
            A.add(row[ti])
    for si in invS:
        row = mul[si]
        for t in S:
            B.add(row[t])
    return 2 * N - len(A) - len(B)


def _anneal(N, d, mul, inv, end, rng):
    """Simulated annealing for S with identity fixed in S (WLOG by left translation)."""
    while time.monotonic() < end:
        S = [0] + rng.sample(range(1, N), d - 1)
        inS = set(S)
        cur = _cost(S, N, mul, inv)
        for it in range(STEPS):
            if cur == 0:
                return S
            if it & 127 == 0 and time.monotonic() > end:
                return None
            T = T0 * (1.0 - it / STEPS) + T1
            i = rng.randrange(1, d)
            x = rng.randrange(1, N)
            if x in inS:
                continue
            old = S[i]
            S[i] = x
            new = _cost(S, N, mul, inv)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
                inS.discard(old)
                inS.add(x)
            else:
                S[i] = old
        if cur == 0:
            return S
    return None


def _search(d, D, base_n, rng, deadline):
    """Search group orders N from the top down; first success is the largest."""
    hi = d * (d - 1) + 1                 # Moore-type cap for |S S^{-1}| = N
    lo = max(base_n // 2 + 1, d + 1)     # need 2N > base_n to improve
    for N in range(hi, lo - 1, -1):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        share = remaining / (N - lo + 1)
        groups = _groups(N, rng)
        per = share / len(groups)
        for mul, inv in groups:
            end = min(time.monotonic() + per, deadline)
            S = _anneal(N, d, mul, inv, end, rng)
            if S is not None:
                edges = [(x, N + mul[x][s]) for x in range(N) for s in S]
                if lib.is_valid(2 * N, edges, d, D):
                    return 2 * N, edges
            if time.monotonic() > deadline:
                return None
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = (n, [(i, (i + 1) % n) for i in range(n)])
        if lib.is_valid(cyc[0], cyc[1], d, D):
            return cyc

    fb = _fallback(d, D)
    if fb is None:
        return 2, [(0, 1)]
    base_n, base_e = fb

    if D != 3 or d < 3:
        return fb

    try:
        res = _search(d, D, base_n, rng, deadline)
    except Exception:
        res = None
    if res is not None:
        return res
    return fb
