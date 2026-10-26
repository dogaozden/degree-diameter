"""Independent check (direct from the definition, no shared code with climb.c).
|(S-S)+(S-S)| = |{a-b+c-d : a,b,c,d in S}| computed in Z_m1 x ... x Z_mk.
Usage: python3 -I verify.py  (runs the example checks below)."""
from itertools import product


def value(mods, S):
    def sub(x, y):
        return tuple((a - b) % m for a, b, m in zip(x, y, mods))
    def add(x, y):
        return tuple((a + b) % m for a, b, m in zip(x, y, mods))
    vals = set()
    for a, b, c, d in product(S, repeat=4):
        vals.add(add(sub(a, b), sub(c, d)))
    return len(vals)


def cyc(n, xs):
    return [(x % n,) for x in xs]


if __name__ == "__main__":
    # Attained: Z_1009, S from climb.c (random_best)
    S = cyc(1009, [871, 226, 458, 758, 780, 473])
    print("Z_1009 example:", value((1009,), S))
    # Free case: Z^6 is not a finite group, so use a large cyclic reduction of the basis:
    # S = {1, 10, 100, 1000, 10^4, 10^5} in Z_m with m huge (m = 10^12+39 prime-ish, distinct
    # values with high probability); value must be 271.
    m = 1000000000039
    S2 = [(x % m,) for x in [1, 10**3, 10**6, 10**9, 10**12 % m, 10**15 % m]]
    print("Z_big (base-1000 digits) example:", value((m,), S2))
