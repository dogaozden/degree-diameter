#!/usr/bin/env python3
"""Counting (Poisson) model of research/frontier/SIZE_LAW.md for Haar graphs at D = 6.
W = K (1 + (K-1)^2 + (K-1)^4) binding words (S S^-1 S S^-1 S), mu = N exp(-W/N) expected misses of a random S,
N_h: first-moment ceiling N exp(-W/N) = K ln N (about N^K sets, each succeeds with prob ~exp(-mu)),
N_star: where mu = mu*(N), ln mu* = 4.34 - 0.123 ln N (the fitted search wall of SIZE_LAW)."""
import math
cells = [(7, 9592), (11, 148944), (13, 388972), (15, 870440), (16, 940846)]
def solve(f, lo, hi):
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) > 0: hi = mid
        else: lo = mid
    return lo
print("K  record  N_needed  W  W/N  mu(N_needed)  N_h(ceiling)  2N_h  N_wall(mu*)  2N_wall")
for K, rec in cells:
    W = K * (1 + (K - 1) ** 2 + (K - 1) ** 4)
    N = rec // 2 + 1
    mu = N * math.exp(-W / N)
    Nh = solve(lambda x: x * math.exp(-W / x) - K * math.log(x), 10, W)
    Nw = solve(lambda x: math.log(x) - W / x - (4.34 - 0.123 * math.log(x)), 10, W)
    print(f"{K:2d} {rec:7d} {N:7d} {W:7d} {W/N:5.3f} {mu:10.1f} {Nh:9.0f} {2*Nh:9.0f} {Nw:9.0f} {2*Nw:9.0f}")
