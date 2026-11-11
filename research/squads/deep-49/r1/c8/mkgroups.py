# Enumerate split metacyclic groups Z_m x|_r Z_k of order N in [LO, HI], deduplicated by the subgroup <r>.
# Usage: python3 mkgroups.py LO HI > groups.txt   (lines "m k r", m >= 2; cyclic groups as m = N, k = 1, r = 1)
import sys
from math import gcd

def prime_powers(n):
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            q = 1
            while n % p == 0:
                n //= p; q *= p
            out.append(q)
        p += 1
    if n > 1:
        out.append(n)
    return out

def groups(N):
    out = []
    seen = set()
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(1, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1:
                continue
            if r == 1:
                key = ('ab', tuple(sorted(pp for n in (m, k) for pp in prime_powers(n))))
            else:
                key = (m, frozenset(pow(r, t, m) for t in range(k)))
            if key in seen:
                continue
            seen.add(key)
            out.append((m, k, r))
    return out

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    if lo <= hi:
        pass
    for N in range(lo, hi + 1):
        for (m, k, r) in groups(N):
            print(m, k, r, N)
