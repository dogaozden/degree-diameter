# Candidate twisted / direct groups in the window 588241..600000 for ORBIT "3 3 1" (needs r of order 3 mod n).
# tpgl q: |G| = n * q(q^2-1), q odd prime.  csl q: |G| = n * q(q^2-1)/2, n even (csl = SL(2,q) x Z_(n/2) if n = 2 mod 4).
# Prints N, whether (Z/n)* has an element of order 3 (alpha can scale Z_n), and the number of fixed z for that scaling.
from math import gcd
def primes(n):
    return [p for p in range(2, n + 1) if all(p % t for t in range(2, int(p ** 0.5) + 1))]
def ordmod(r, n):
    k, y = 1, r % n
    while y != 1 % n:
        y = y * r % n; k += 1
    return k
LO, HI = 588241, 600000
rows = []
for q in [3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31]:
    if q in (9, 25, 27):
        continue  # prime powers not handled for tpgl (odd prime q only in the screen)
    pg = q * (q * q - 1)
    for n in range(1, HI // pg + 2):
        N = n * pg
        if not (LO <= N <= HI):
            continue
        # order-3 scalings r of Z_n with the most fixed points
        best = None
        for r in range(2, n):
            if gcd(r, n) == 1 and pow(r, 3, n) == 1:
                fx = gcd(r - 1, n)
                if best is None or fx < best[1]:
                    best = (r, fx)
        if best is None:
            rows.append(("tpgl", q, n, N, "no order-3 scaling of Z_n"))
        else:
            rows.append(("tpgl", q, n, N, "r=%d fixz=%d" % best))
    for n in range(2, 2 * HI // (q * (q * q - 1)) + 4, 2):
        N = n * q * (q * q - 1) // 2
        if not (LO <= N <= HI):
            continue
        rows.append(("csl", q, n, N, "n mod 4 = %d%s" % (n % 4, "  (== sl %d x Z_%d)" % (q, n // 2) if n % 4 == 2 else "")))
for row in rows:
    print("%-5s q=%-3d n=%-4d N=%-7d %s" % row)
