"""Check the first-order deficiency 1 - n/M_b = c/q + O(q^-2) of BUILDINGS.md Theorem 4: prints q (1 - n/M_b) for
large primes q (exact rational arithmetic), which must tend to c = t(h-2) (balanced, equal parameters, t = r/2),
r(h-2) (Delorme products), 10 (2E6)."""
import sys
from fractions import Fraction
sys.path.insert(0, '.')
from rates import E, DEG, E_2E6
def Mb(d, D): return 2 * sum((d - 1) ** i for i in range(D))
QS = [1009, 10007, 100003]
cases = [
    ("A4 direct", lambda q: (2 * E(DEG['A'](4), q) // (q + 1) ** 2, (q + 1) ** 2), 5, 2 * 3),
    ("A6 direct", lambda q: (2 * E(DEG['A'](6), q) // (q + 1) ** 3, (q + 1) ** 3), 7, 3 * 5),
    ("C4 direct", lambda q: (2 * E(DEG['B'](4), q) // (q + 1) ** 2, (q + 1) ** 2), 8, 2 * 6),
    ("F4 direct", lambda q: (2 * E(DEG['F4'], q) // (q + 1) ** 2, (q + 1) ** 2), 12, 2 * 10),
    ("E6 direct", lambda q: (2 * E(DEG['E6'], q) // (q + 1) ** 3, (q + 1) ** 3), 12, 3 * 10),
    ("E8 direct", lambda q: (2 * E(DEG['E8'], q) // (q + 1) ** 4, (q + 1) ** 4), 30, 4 * 28),
    ("2E6 direct", lambda q: (2 * E_2E6(q) // ((q + 1) * (q * q + 1)), (q + 1) * (q * q + 1)), 12, 10),
    ("A3 x Opp", lambda q: (2 * E(DEG['A'](3), q) ** 2 // (q + 1) ** 3, (q + 1) ** 3), 4, 3 * 2),
    ("B5 x Opp", lambda q: (2 * E(DEG['B'](5), q) ** 2 // (q + 1) ** 5, (q + 1) ** 5), 10, 5 * 8),
    ("G2 direct (Moore)", lambda q: (2 * E(DEG['G2'], q) // (q + 1), q + 1), 6, 0),
]
for nm, f, D, c in cases:
    vals = []
    for q in QS:
        n, d = f(q); defic = 1 - Fraction(n, Mb(d, D)); vals.append(f"q={q}: q(1-n/M)={float(q * defic):.4f}")
    print(f"{nm:18s} D={D:2d} predicted c={c:4d}   " + "  ".join(vals))

# Ree-Tits octagons GO(q, q^2), q = 2^(2e+1): Delorme product (bipartite, D = 8) and quotient (general, D <= 7).
def M(d, D): return 1 + d * sum((d - 1) ** i for i in range(D))
print("Ree-Tits octagons GO(q,q^2): points (1+q)(1+q^3)(1+q^6), lines (1+q^2)(1+q^3)(1+q^6)")
for q in (2, 8, 32, 128, 512, 2048):
    s, t = q, q * q
    P = (1 + s) * (1 + s * t) * (1 + s * s * t * t); L = (1 + t) * (1 + s * t) * (1 + s * s * t * t)
    d = (1 + s) * (1 + t)
    print(f"  q={q}: Delta={d}: product 2|P||L| / M_b(Delta,8) = {2 * P * L / Mb(d, 8):.4f};"
          f"  quotient |P||L| / M(Delta,7) = {P * L / M(d, 7):.4f}")
