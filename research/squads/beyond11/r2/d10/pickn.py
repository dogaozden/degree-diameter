import math, sys
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isprime(x):
    return x >= 2 and all(x % i for i in range(2, int(x**0.5) + 1))
d, D = int(sys.argv[1]), int(sys.argv[2])
target = float(sys.argv[3])
w = W(d, D)
for n in [1, 7, 31, 127, 433, 509, 547]:
    if n > 1 and not (isprime(n) and n % 3 == 1):
        print(f"n={n}: not usable with k=3 (prime and = 1 mod 3 needed)"); continue
    best = []
    for p in range(5, 2000):
        if not isprime(p) or n % p == 0 and n > 1 and p == n: continue
        if math.gcd(p, n) != 1: continue
        for fam, base in (("psl", p*(p*p-1)//2), ("sl", p*(p*p-1))):
            N = base * n
            mu = N * math.exp(-w / N)
            best.append((abs(mu - target), fam, p, n, N, mu))
    best.sort()
    for b in best[:3]:
        print(f"n={n} {b[1]} p={b[2]} N={b[4]} 2N={2*b[4]} mu={b[5]:.2f}")
