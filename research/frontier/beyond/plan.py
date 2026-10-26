#!/usr/bin/env python3
"""Plan for the new cells beyond the 2013 table (job new-cells-beyond, 2026-10-26).

Cells: Delta = 17..20 at D = 3..10, and D = 11, 12 at Delta = 3..10.
Prints, per cell: bipartite Moore bound, upper bound used, the trivial floor from monotonicity
(n_b(Delta-1, D) and n_b(Delta, D-1) from our records / the table), formula-family values, and the Haar
order N (group order, graph 2N) at which mu = N exp(-W/N) equals 1, 5 and 20 (SIZE_LAW.md).
"""
import math, sys

def moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))

def upper(d, D):
    # Prop. 6.4 of Feria-Puron & Pineda-Villavicencio (DAM 2012): n_b <= M_b - 6 for d >= 3, 5 <= D <= 187, D != 6.
    # D = 3, 4, 6: Moore bound (the needed generalized polygons exist, or their existence is open, for d = 17..20).
    if D in (3, 4, 6):
        return moore(d, D)
    return moore(d, D) - 6

def W(d, D):
    if D % 2 == 0:
        return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))

def n_at_mu(d, D, mu):
    w = W(d, D); lo, hi = 1.0, 1e14
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if mid * math.exp(-w / mid) < mu: lo = mid
        else: hi = mid
    return lo

def prime_powers(lim):
    out = []
    for q in range(2, lim + 1):
        for p in range(2, q + 1):
            if all(p % r for r in range(2, int(p ** 0.5) + 1)):
                if q % p == 0:
                    x = q
                    while x % p == 0: x //= p
                    if x == 1: out.append(q)
                    break
    return out

PP = set(prime_powers(64))
def gq(q): return 2 * (q + 1) * (q * q + 1)                 # |W(q)| incidence graph
def gh(q): return 2 * (q ** 6 - 1) // (q - 1)               # |H(q)|
def pg(q): return 2 * (q * q + q + 1)

def formulas(d, D):
    """(value, description) for the formula families that apply to (d, D)."""
    f = []
    if D == 3:
        if d - 1 in PP: f.append((pg(d - 1), f"PG(2,{d-1}) incidence graph (Moore)"))
        if d - 2 in PP and d - 2 >= 4: f.append((2 * ((d - 2) ** 2 + (d - 2) + 6), f"fourth hat, q={d-2} (POLISHED Thm 2.2)"))
    if D == 4:
        if d - 1 in PP: f.append((gq(d - 1), f"W({d-1}) incidence graph (Moore)"))
        for q in sorted(PP):
            if q <= d - 1: f.append((2 * q * q * d, f"Thm B, q={q}: 2q^2 Delta"))
        if d - 2 in PP and (d - 2) % 2: f.append((2 * (d - 2) ** 2 * d, f"Thm A, q={d-2}"))
    if D == 6:
        if d - 1 in PP: f.append((gh(d - 1), f"H({d-1}) incidence graph (Moore)"))
        for m in range(2, 5):
            q = d - m
            if q in PP and q >= 3:
                v = gh(q) + (m - 1) * (2 * q**4 + 2 * q**3 + 2 * q + 2 + m * (q**3 + q + 2) + m * m)
                f.append((v, f"Thm D, q={q}, m={m}"))
    if D in (5, 7):
        base = gq if D == 5 else gh
        nm = "W" if D == 5 else "H"
        for q in sorted(PP):
            j = d - q - 1
            if j >= 0: f.append(((2 * j + 1) * base(q), f"polygon cover {2*j+1}x{nm}({q}) (j={j})"))
            if D == 5 and j == 2: f.append((6 * gq(q) // 1, f"doubled matching 6x W({q}) (DM_D5, annealed)"))
    if D == 5 and d % 4 == 0 and (d // 4) in PP:
        q = d // 4
        f.append((2 * 66 * q ** 4, f"route chart 4 letters x F{q}, m=66 controller (2*m*q^4)"))
    if D == 8:
        for q in sorted(PP):
            j = d - q - 1
            if j == 2: f.append((10 * gh(q), f"polygon cover n+2: 10x H({q})"))
            if j >= 1:
                v = (2 * j + 1) * ((q - 1) // 2 + 3 * (j - 1)) * gh(q)
                f.append((v, f"PATTERN q={q}, j={j}"))
    f.sort(reverse=True)
    return f

# our current values (Delta <= 16, D <= 10), README of master c48c976
OURS = {}
TABLE = """3 14 30 56 126 168 288 506 800
4 26 80 162 728 864 2184 4970 12416
5 42 170 354 2730 3120 9760 29756 95472
6 62 312 684 7812 8880 31680 127296 524160
7 80 359 1152 9592 23598 95760 462840 2237760
8 114 800 2048 39216 43344 239904 1341600 7818096
9 146 1170 2662 74898 118238 546720 3499776 23975280
10 182 1640 4800 132860 225152 1176480 8003856 60141120
11 192 1782 7020 148944 413180 2258520 16792080 148729680
12 266 2928 9840 354312 693500 4650100 34026720 325832976
13 276 3146 11486 388972 1064472 6999552 67742688 677714400
14 366 4760 17568 804468 1789588 14172480 116068656 1326627120
15 376 5070 20736 870440 2501491 18128880 208029120 2467618800
16 396 5440 33792 940846 4052108 36201060 337394400 4708566360"""
for line in TABLE.splitlines():
    a = list(map(int, line.split()))
    for D, v in zip(range(3, 11), a[1:]): OURS[(a[0], D)] = v

CELLS = [(d, D) for d in range(17, 21) for D in range(3, 11)] + [(d, D) for D in (11, 12) for d in range(3, 11)]

if __name__ == "__main__":
    for d, D in CELLS:
        fl = [(OURS.get((d - 1, D)), f"({d-1},{D})"), (OURS.get((d, D - 1)), f"({d},{D-1})")]
        fl = [x for x in fl if x[0]]
        best_floor = max(fl) if fl else (0, "-")
        h = {mu: 2 * n_at_mu(d, D, mu) for mu in (1, 5, 20)}
        print(f"({d},{D}) Moore {moore(d,D):,} upper {upper(d,D):,} | floor {best_floor[0]:,} {best_floor[1]} | "
              f"Haar 2N at mu=1/5/20: {h[1]:.3g} / {h[5]:.3g} / {h[20]:.3g}")
        for v, s in formulas(d, D)[:3]:
            print(f"      {v:,}  {s}")
