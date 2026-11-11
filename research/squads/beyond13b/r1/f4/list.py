# List odd-order products F1 x F2 (F1 = Z_m1 x|_r1 Z_k1 from a fixed list, F2 = Z_m x|_r Z_k, m prime, k odd prime 11..61,
# k | m-1, r of order k) with N = m1 k1 m2 k2 in [LO, HI]; print mu = N exp(-W/N).
import math, sys

LO, HI, W = 1798000, 1950000, 22369621
F1 = [(11, 4, 5), (7, 2, 3), (13, 3, 3), (31, 2, 5), (29, 7, 7), (23, 2, 11), (53, 10, 13)]
KS = [k for k in range(11, 62) if all(k % d for d in range(2, int(k ** 0.5) + 1))]  # primes 11..61

def isprime(n):
    if n < 2:
        return False
    for d in range(2, int(n ** 0.5) + 1):
        if n % d == 0:
            return False
    return True

def primroot(m):
    phi = m - 1
    fac = [p for p in range(2, phi + 1) if phi % p == 0 and isprime(p)]
    for g in range(2, m):
        if all(pow(g, phi // p, m) != 1 for p in fac):
            return g
    raise ValueError(m)

def f2_list(lo, hi):
    out = []
    for k in KS:
        # m prime, m == 1 mod k, m*k in [lo, hi]
        mlo = max(3, -(-lo // k)); mhi = hi // k
        for m in range(mlo, mhi + 1):
            if (m - 1) % k or not isprime(m):
                continue
            g = primroot(m)
            r = pow(g, (m - 1) // k, m)
            assert pow(r, k, m) == 1 and r != 1, (m, k, r)
            out.append((m, k, r))
    return out

rows = []
for (m1, r1, k1) in F1:
    n1 = m1 * k1
    lo2 = -(-LO // n1); hi2 = HI // n1
    for (m2, k2, r2) in f2_list(lo2, hi2):
        N = n1 * m2 * k2
        if LO <= N <= HI:
            mu = N * math.exp(-W / N)
            rows.append((mu, N, (m1, k1, r1), (m2, k2, r2)))
rows.sort(reverse=True)
for mu, N, a, b in rows:
    print(f"mu={mu:.4f} N={N} 2N={2*N} F1=meta {a[0]} {a[1]} {a[2]} (order {a[0]*a[1]}) F2=meta {b[0]} {b[1]} {b[2]} (order {b[0]*b[1]}) cmd: prod meta {a[0]} {a[1]} {a[2]} meta {b[0]} {b[1]} {b[2]} 1")
print("total", len(rows), file=sys.stderr)
