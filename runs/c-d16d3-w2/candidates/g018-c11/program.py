"""Diameter-3 bipartite search via group Haar graphs (non-cyclic groups included).

Construction: for a finite group G of order m and a k-subset S of G, the graph with
A-vertices g, B-vertices h, and edges g ~ h*s^{-1}... (equivalently g ~ g*s on the B side)
is k-regular on 2m vertices. It has diameter 3 whenever S*S^{-1} = G and S^{-1}*S = G.
Cyclic groups give the old difference-cover search. This version also searches
semidirect products Z_M x| Z_K, which can cover more of G than cyclic groups can.
Orders are tried in increasing order from near the Moore-type cap k(k-1)+1, and the
largest order found is returned. A projective-plane incidence graph and K_{d,d} are
fallbacks, and every candidate is checked with lib.is_valid.

Scope: D >= 3 uses the group search. D = 2 returns K_{d,d}. D = 1 returns K_2.
The C_SOURCE below is a small pass-through placeholder and is not invoked; the
Python search is fast enough for these sizes.
"""
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
int main(void) {
    int c;
    while ((c = getchar()) != EOF) putchar(c);
    return 0;
}
"""


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _tables(M, K, r, m):
    """Multiplication table (flat list, index x*m+y) and inverse list for Z_M x| Z_K."""
    order, mul, inv = lib.semidirect_group(M, K, r)
    if order != m:
        raise ValueError("order mismatch")
    MT = [0] * (m * m)
    for x in range(m):
        base = x * m
        for y in range(m):
            MT[base + y] = mul(x, y)
    INV = [inv(x) for x in range(m)]
    return MT, INV


def _groups(m, rng):
    """Candidate (M, K, r) with M*K = m: cyclic first, then random non-cyclic and abelian options."""
    out = [(m, 1, 1)]
    cand = []
    for K in range(2, min(16, m // 2) + 1):
        if m % K:
            continue
        M = m // K
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, K, M) == 1 % M:
                cand.append((M, K, r))
    rng.shuffle(cand)
    return out + cand[:60]


def _contrib(e, others, sgn, cA, cB, m, MT, INV):
    """Add (sgn=+1) or remove (sgn=-1) the ordered-pair contributions of element e against others.

    cA counts products s*t^{-1}, cB counts s^{-1}*t, over ordered pairs s != t.
    Returns the change in the number of zero entries (indices 1..m-1) in cA and cB.
    Index 0 is never touched because s != t.
    """
    ie = INV[e]
    dz = 0
    for t in others:
        it = INV[t]
        for arr, x in ((cA, MT[e * m + it]), (cA, MT[t * m + ie]),
                       (cB, MT[ie * m + t]), (cB, MT[it * m + e])):
            old = arr[x]
            new = old + sgn
            arr[x] = new
            if old == 0:
                dz -= 1
            elif new == 0:
                dz += 1
    return dz


def _cover(m, k, MT, INV, deadline, rng):
    """Simulated annealing for a k-subset S of G with S S^{-1} = G and S^{-1} S = G. Returns S or None."""
    while time.monotonic() < deadline:
        cA = [0] * m
        cB = [0] * m
        zeros = 2 * (m - 1)
        S = []
        for e in rng.sample(range(m), k):
            zeros += _contrib(e, S, 1, cA, cB, m, MT, INV)
            S.append(e)
        steps = 0
        while zeros:
            steps += 1
            if steps % 2048 == 0 and time.monotonic() > deadline:
                return None
            if steps > 150000:
                break  # restart from a fresh random set
            i = rng.randrange(k)
            y = rng.randrange(m)
            if y in S:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            dz = _contrib(old, others, -1, cA, cB, m, MT, INV)
            dz += _contrib(y, others, 1, cA, cB, m, MT, INV)
            if dz <= 0 or rng.random() < math.exp(-dz / 0.3):
                S[i] = y
                zeros += dz
            else:
                _contrib(y, others, -1, cA, cB, m, MT, INV)
                _contrib(old, others, 1, cA, cB, m, MT, INV)
        if zeros == 0:
            return S
    return None


def _level(m, k, deadline, rng):
    """Try to find a valid group Haar graph of order m (2m vertices). Returns (n, edges) or None."""
    groups = _groups(m, rng)
    cache = {}
    while time.monotonic() < deadline:
        for idx, (M, K, r) in enumerate(groups):
            if time.monotonic() >= deadline:
                break
            if idx not in cache:
                try:
                    cache[idx] = _tables(M, K, r, m)
                except ValueError:
                    cache[idx] = None
                    continue
            if cache[idx] is None:
                continue
            MT, INV = cache[idx]
            gd = min(deadline, time.monotonic() + 4.0)
            S = _cover(m, k, MT, INV, gd, rng)
            if S is not None:
                edges = [(g, m + MT[g * m + s]) for g in range(m) for s in S]
                return 2 * m, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Projective-plane fallback (diameter 3, valid for every D >= 3).
    pg = _pg_fallback(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Main search: group Haar graphs of order m with a k-set covering both difference sides.
    k = d
    cap = k * (k - 1) + 1
    if k >= 2 and cap >= 3:
        lo = max(k + 1, int(0.78 * cap))
        for m in range(lo, cap + 1):
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 1.0:
                break
            level_dl = now + max(1.5, 0.4 * remaining)
            res = _level(m, k, level_dl, rng)
            if res is None:
                break
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
