"""List SL(2,p) x Z_n and PSL(2,p) x Z_n (p prime) with N = |G| in a window, for a Haar search at (d, D).

mu = N exp(-W/N) (../frontier/SIZE_LAW.md), W = number of binding words.  For the k-orbit method
(../structured/STRUCTURE.md) every prime factor of n should be = 1 mod k, so that z -> r z of order k fixes only 0.
n is capped at NMAX: big cyclic factors mix badly (STRUCTURE.md section 5).
Usage: mu_list.py d D LO HI [k] [NMAX]
"""
import math
import sys


def W(d, D):
    if D % 2:
        k = (D - 1) // 2
        return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, k + 1))
    return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))


def primes(m):
    s = bytearray([1]) * (m + 1)
    s[0] = s[1] = 0
    for i in range(2, int(m ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(m + 1) if s[i]]


def factor(n):
    f, x, t = [], n, 2
    while t * t <= x:
        while x % t == 0:
            f.append(t)
            x //= t
        t += 1
    if x > 1:
        f.append(x)
    return f


if __name__ == "__main__":
    d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
    k = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    nmax = int(sys.argv[6]) if len(sys.argv) > 6 else 3000
    w = W(d, D)
    rows = []
    for p in primes(3000):
        if p < 5:
            continue
        for fam, o in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
            if o > hi:
                continue
            for n in range(max(1, int(lo // o)), min(int(hi // o) + 2, nmax + 1)):
                N = o * n
                if not (lo <= N <= hi):
                    continue
                if n > 1 and any(q % k != 1 for q in factor(n)):
                    continue
                if n % p == 0:
                    continue
                cg = (p - 1) if p % 3 == 1 else (p + 1)
                rows.append((N, fam, p, n, N * math.exp(-w / N), cg))
    rows.sort()
    for N, fam, p, n, mu, cg in rows:
        print(f"{fam:4s} {p:5d} n {n:5d}  N {N:14,d}  2N {2 * N:15,d}  mu {mu:7.2f}  mu/{k} {mu / k:6.2f}  |C(g)| {cg}")
