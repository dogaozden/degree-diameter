import sys
from math import gcd
lo, hi = 6578094, 6660000
def isprime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True
def primroot(m):
    # factor m-1
    n = m-1; fs = []; p = 2
    while p*p <= n:
        if n % p == 0:
            fs.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: fs.append(n)
    for g in range(2, m):
        if all(pow(g, (m-1)//q, m) != 1 for q in fs): return g
out = []
for k in range(41, 102):
    for m in range(-(-lo//k), hi//k + 1):
        if (m-1) % k: continue
        if not isprime(m): continue
        g = primroot(m)
        r = pow(g, (m-1)//k, m)
        out.append((m*k, m, k, r))
out.sort()
for N, m, k, r in out:
    print(N, m, k, r)
