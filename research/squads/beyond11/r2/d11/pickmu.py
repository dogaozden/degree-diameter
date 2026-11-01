import math, sys
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isprime(x):
    return x >= 2 and all(x % i for i in range(2, int(x**0.5) + 1))
d, D = int(sys.argv[1]), int(sys.argv[2])
w = W(d, D)
for n in [1, 7, 127, 499]:
    for fam in ["psl", "sl"]:
        best = None
        for p in range(5, 3000):
            if not isprime(p) or math.gcd(p, n) != 1: continue
            base = p * (p * p - 1) // (2 if fam == "psl" else 1)
            N = base * n
            if N > 3e8: break
            mu = N * math.exp(-w / N)
            if 2 <= mu <= 120:
                if best is None or abs(math.log(mu/16)) < abs(math.log(best[1]/16)):
                    best = (p, mu, N)
        print(d, D, n, fam, best)
