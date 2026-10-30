#!/usr/bin/env python3
"""find_beta_meta.py m k r "i,j ...": involutory automorphisms beta(x) = x^u, beta(y) = x^t y^v of
G = <x, y | x^m = y^k = 1, y x y^-1 = x^r> with psi(S) = S, psi(g) = beta(g)^-1 (S self-dual).  Prints (u, t, v)."""
import sys
from math import gcd
m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
S = [tuple(int(t) for t in p.split(",")) for p in sys.argv[4].split()]
rp = [pow(r, j, m) for j in range(k)]
mul = lambda g, h: ((g[0] + rp[g[1]] * h[0]) % m, (g[1] + h[1]) % k)
def pw(g, e):
    a = (0, 0)
    for _ in range(e): a = mul(a, g)
    return a
inv = lambda g: ((-rp[(-g[1]) % k] * g[0]) % m, (-g[1]) % k)
for u in range(1, m):
    if gcd(u, m) != 1: continue
    for v in range(1, k):
        if gcd(v, k) != 1: continue
        for t in range(m):
            bx, by = (u, 0), (t, v)
            if mul(mul(by, bx), inv(by)) != pw(bx, r) or pw(by, k) != (0, 0): continue
            beta = lambda g: mul(pw(bx, g[0]), pw(by, g[1]))
            if beta(beta((1, 0))) != (1, 0) or beta(beta((0, 1))) != (0, 1): continue
            if {inv(beta(s)) for s in S} == set(S): print(u, t, v)
