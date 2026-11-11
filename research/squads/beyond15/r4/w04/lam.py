#!/usr/bin/env python3
"""lam.py n k : primes n, list of lambda of exact order k mod n (k | n-1), smallest first"""
import sys
n, k = int(sys.argv[1]), int(sys.argv[2])
out = []
for g in range(2, n):
    l = pow(g, (n - 1) // k, n)
    if l != 1 and all(pow(l, k // p, n) != 1 for p in range(2, k + 1) if k % p == 0 and all(p % q for q in range(2, p))):
        out.append(l)
        break
print(out[0] if out else -1)
