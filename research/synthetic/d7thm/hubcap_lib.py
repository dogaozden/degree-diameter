"""Shared helpers for hubcap.py / hubsum.py (D7_THEOREMS.md Section 5)."""
from functools import lru_cache

def _prime_powers(limit):
    sieve = bytearray([1]) * (limit + 1); sieve[0] = sieve[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    pp = set()
    for p in range(2, limit + 1):
        if sieve[p]:
            x = p
            while x <= limit:
                pp.add(x); x *= p
    return sorted(pp)
PP = _prime_powers(5000)

def K0(s):
    """points (= lines) of a generalized hexagon of order (s, s)"""
    return (s + 1) * (s ** 4 + s ** 2 + 1)

def slots(q, k, m=None):
    """(K_B, K_A) of Theorem 3.4 for the alternating layout, P = (q+1)(q^3+1), Lam = q^4+q^2+q, m = q^2+1"""
    P = (q + 1) * (q ** 3 + 1); Lam = q ** 4 + q ** 2 + q
    if m is None: m = q * q + 1
    a = k // 2
    if k % 2 == 0:
        return a * (Lam + m), a * (Lam + m)
    return a * P + (a + 1) * m, a * Lam + (a + 1) * m

@lru_cache(maxsize=None)
def tree_intervals(d):
    """Lemma 7.1 of D7_HEXAGON.md: for each prime power s <= d-1, sizes [s^2+s+1, (s^2+s+1)(1+t+tu)] with
    t = d-s-1, u = d-1 (each colour independently)."""
    iv = []
    for s in PP:
        if s > d - 1: break
        n = s * s + s + 1; t = d - s - 1; u = d - 1
        iv.append((n, n * (1 + t + t * u)))
    return iv

@lru_cache(maxsize=None)
def kappa_cover(d):
    """largest X such that every K in [7, X] lies in some interval of tree_intervals(d) (0 if 7 is not covered)"""
    iv = sorted(tree_intervals(d))
    reach = 6
    for lo, hi in iv:
        if lo <= reach + 1:
            reach = max(reach, hi)
    return reach if reach >= 7 else 0

def kappa_tab(d):
    return [kappa_cover(x) if x >= 2 else 0 for x in range(d + 1)]

def tree_ok(K1, K2, d):
    """Plane with pendant trees (D7_HEXAGON.md Lemma 7.1), colour classes sized independently: a core PG(2,s)
    (n = s^2+s+1 points and lines), c_P depth-1 children under points and c_L under lines (at most t = d-s-1 per core
    vertex), g_P depth-2 children under the point-children and g_L under the line-children (at most u = d-1 each).
    Colour A (with the core points): n + c_L + g_P; colour B: n + c_P + g_L.  Returns (s, c_P, c_L, g_P, g_L) or None.
    For fixed s, taking c_P as large as possible only loosens the conditions, so one value of c_P suffices."""
    for s in PP:
        if s + 1 > d: break
        n = s * s + s + 1
        if n > min(K1, K2): break
        t = d - s - 1; u = d - 1
        cP = min(t * n, K2 - n)
        lo = max(0, K1 - n - u * cP, -(-(K2 - n - cP) // u) if u > 0 else (0 if K2 - n - cP <= 0 else 10 ** 18))
        hi = min(t * n, K1 - n)
        if lo <= hi:
            cL = lo
            gP = K1 - n - cL; gL = K2 - n - cP
            assert 0 <= gP <= u * cP and 0 <= gL <= u * cL and cP <= t * n and cL <= t * n
            return (s, cP, cL, gP, gL)
    return None
