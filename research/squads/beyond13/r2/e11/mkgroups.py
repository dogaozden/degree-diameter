# find metacyclic groups Z_m x|_r Z_k with m prime, m = 1 mod k, |G| = m k near 93157 (N per side)
import sys
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
target = 93157
out = []
for k in [3, 5, 7, 9, 11, 13, 17, 19, 23, 29, 37]:
    best = None
    m0 = target // k
    for d in range(0, 5000):
        for m in (m0 + d, m0 - d):
            if m > 2 and (m - 1) % k == 0 and isprime(m):
                best = m; break
        if best: break
    m = best
    # element of order k mod m
    fac = []
    n = m - 1; p = 2
    while p * p <= n:
        if n % p == 0:
            fac.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: fac.append(n)
    g = next(x for x in range(2, m) if all(pow(x, (m - 1) // q, m) != 1 for q in fac))
    r = pow(g, (m - 1) // k, m)
    assert pow(r, k, m) == 1 and r != 1
    out.append((k, m, r))
    print(k, m, r, m * k)
# cyclic control
print(1, 93157, 1, 93157)
