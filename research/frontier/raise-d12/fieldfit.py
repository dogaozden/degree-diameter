"""fieldfit.py: for even D and degree d, list G = Q x Z_n with Q in {SL(2,32) (field automorphism of order 5),
SL(2,128) (order 7), PSL(2,243) (order 5)}, n = 1 or n with an element of order k mod n (all prime factors = 1 mod k)
and gcd(n, |T|) = 1, and an orbit structure d = f + k m with f in {0, 1, 2}; print those with mu/k <= MAX (default 6),
mu = N exp(-W/N) (W = odd words <= D-1).  The (8..10,12) finds sit at mu/k = 4.0, 4.9, 5.1."""
import math, sys
def W(d, D): return sum(d * (d - 1) ** (j - 1) for j in range(1, D, 2))
Qs = [("sl 32", 32736, 5, 31), ("sl 128", 2097024, 7, 127), ("psl 243", 7174332, 5, 121)]
def okn(n, k, T):
    if n == 1: return True
    if math.gcd(n, T) != 1: return False
    x = n; p = 2
    while p * p <= x:
        if x % p == 0:
            if (p - 1) % k: return False
            while x % p == 0: x //= p
        p += 1
    return x == 1 or (x - 1) % k == 0
MAX = float(sys.argv[1]) if len(sys.argv) > 1 else 6
for D in (8, 10, 12, 14):
    for d in range(3, 21):
        w = W(d, D)
        for name, q, k, T in Qs:
            for f in (0, 1, 2):
                if (d - f) % k or d - f <= 0: continue
                for n in range(1, 5000):
                    if not okn(n, k, T): continue
                    N = q * n; lam = w / N
                    if lam > 60: continue
                    mu = N * math.exp(-lam)
                    if mu / k <= MAX and mu / k >= 0.5:
                        print(f"(d,D)=({d},{D}) {name} x Z{n} ORBIT '{k} {(d-f)//k} {f}' 2N={2*N:,} mu={mu:.1f} mu/k={mu/k:.1f}")
