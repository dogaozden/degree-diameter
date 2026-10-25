"""List SL(2,p) x Z_n and PSL(2,p) x Z_n for the k-orbit method with any odd prime-power-free k (3, 5, 15, ...).

Unlike mu_list.py this checks that (P)SL(2,p) has an element of order k mod +-I (k | (p-1)/2 or k | (p+1)/2), every
prime factor of n is = 1 mod k, and it prints the fixed-point penalty F = |Fix(alpha)| e^(-lambda/k)
(|Fix| = torus = p -+ 1 for SL, (p -+ 1)/2 for PSL; ../structured/STRUCTURE.md section 1) and mu_eff = mu/k + F.
Usage: klist.py d D LO HI k [PMIN] [PMAX] [NMAX] [REC]   (REC: record vertex count for the "+%" column)
"""
import math
import sys
from mu_list import W, primes, factor

if __name__ == "__main__":
    d, D, lo, hi, k = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    pmin = int(sys.argv[6]) if len(sys.argv) > 6 else 7
    pmax = int(sys.argv[7]) if len(sys.argv) > 7 else 400
    nmax = int(sys.argv[8]) if len(sys.argv) > 8 else 10 ** 7
    rec = float(sys.argv[9]) if len(sys.argv) > 9 else 0
    w = W(d, D)
    rows = []
    for p in primes(pmax):
        if p < max(pmin, 5):
            continue
        tor = [t for t in (p - 1, p + 1) if (t // 2) % k == 0]
        if not tor:
            continue
        for fam, o in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
            fix = tor[0] // 2 if fam == "psl" else tor[0]
            for n in range(max(1, int(lo // o)), min(int(hi // o) + 2, nmax + 1)):
                N = o * n
                if not (lo <= N <= hi) or n % p == 0 or (n > 1 and any(q % k != 1 for q in factor(n))):
                    continue
                lam = w / N
                mu = N * math.exp(-lam)
                F = fix * math.exp(-lam / k)
                rows.append((N, fam, p, n, mu, F, fix))
    rows.sort()
    for N, fam, p, n, mu, F, fix in rows:
        gain = " (%+.2f%%)" % ((2 * N / rec - 1) * 100) if rec else ""
        print("%-4s %4d n %7d  N %14d  2N %15d%s  mu %6.2f  F %5.2f  mu_eff %6.2f  |Fix| %d"
              % (fam, p, n, N, 2 * N, gain, mu, F, mu / k + F, fix))
