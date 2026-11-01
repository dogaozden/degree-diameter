import sys, math
lo, hi = int(sys.argv[1]), int(sys.argv[2])
klo, khi = int(sys.argv[3]), int(sys.argv[4])
def phi(n):
    r, x, p = n, n, 2
    while p * p <= x:
        if x % p == 0:
            while x % p == 0: x //= p
            r -= r // p
        p += 1
    if x > 1: r -= r // x
    return r
def isprime(n):
    return n > 1 and all(n % p for p in range(2, int(n**0.5) + 1))
res = []
for k in range(klo, khi + 1, 2):
    m = lo // k
    while m * k <= hi:
        mm = m
        if mm >= 3 and mm % 2 == 1 and mm * k >= lo and phi(mm) % k == 0:
            # faithful-ish r of order k: try generators
            best = None
            for g in range(2, mm):
                if math.gcd(g, mm) != 1: continue
                r = pow(g, phi(mm) // k, mm)
                if r == 1: continue
                # order of r
                o, x = 1, r
                while x != 1 and o <= k: x = x * r % mm; o += 1
                if o == k: best = r; break
            if best is not None:
                res.append((mm * k, mm, k, best, isprime(mm)))
        m += 1
for row in sorted(res):
    print(*row)
