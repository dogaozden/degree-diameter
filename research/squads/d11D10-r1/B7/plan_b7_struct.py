"""Structure check for B7: how many distinct Z-exponent classes the binding walks can take, and the implied loss.
For G = H x Z_n every walk's Z-value is a fixed linear form c.z in the orbit-letter Z-values, so walks with the same
exponent vector c share their Z-value. Per H-value h the number of distinct classes hit is E|C_h| = sum_c (1-exp(-M_c/|H|)),
at most K' = #{c in Z^d : |c|_1 <= 9} (d = number of orbit letters: 9 for k=3, 10 for k=5). With M_c = W/K' (uniform, the
best case for the model) the effective exponent is lam_eff = lam (1-exp(-x))/x, x = W/(K'|H|), and mu grows by exp(lam - lam_eff).
"""
import math, sys
sys.path.insert(0, '.')
from math import comb
W = 1111111111


def ball(d, r):
    return sum(2 ** j * comb(d, j) * comb(r, j) for j in range(0, min(d, r) + 1))


Kp = {3: ball(9, 9), 5: ball(10, 9)}
print("K' (orbit-letter Z-classes, l1-ball radius 9): k=3 d=9 -> %d ; k=5 d=10 -> %d" % (Kp[3], Kp[5]))


def ratio(H, k):
    x = W / (Kp[k] * H)
    return x, (1 - math.exp(-x)) / x


for H in (660, 1320, 3420, 6840, 12180, 24360, 32736, 60000, 113460, 178380, 246480, 493920, 1000000, 5000000):
    x5, r5 = ratio(H, 5)
    x3, r3 = ratio(H, 3)
    print("|H| = %8d  k=5: x = %.4f, lam_eff/lam = %.3f, mu x %.2f | k=3: x = %.4f, ratio %.3f, mu x %.2f"
          % (H, x5, r5, math.exp(14.1 * (1 - r5)), x3, r3, math.exp(14.1 * (1 - r3))))
