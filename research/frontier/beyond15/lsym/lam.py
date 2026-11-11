#!/usr/bin/env python3
"""lam.py n k: all lambda in Z_n^* with lambda^k = 1 (one per cyclic subgroup <lambda> of order exactly k listed first)."""
import sys, math
n, k = int(sys.argv[1]), int(sys.argv[2])
sols = [l for l in range(1, n) if math.gcd(l, n) == 1 and pow(l, k, n) == 1]
exact = [l for l in sols if all(pow(l, j, n) != 1 for j in range(1, k))]
print('exact order', k, ':', exact[:8], '... all:', len(sols))
