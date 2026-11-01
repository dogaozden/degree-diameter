import math, sys
sys.argv += []
exec(open('pickn.py').read().split('d, D = ')[0])
d, D, target = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
w = W(d, D)
for n in [1, 7, 31, 127, 433]:
    for fam in ("psl", "sl"):
        c = []
        for p in range(5, 1000):
            if not isprime(p) or math.gcd(p, n) != 1: continue
            base = p*(p*p-1)//2 if fam == "psl" else p*(p*p-1)
            N = base * n
            mu = N * math.exp(-w / N)
            mu=max(mu,1e-9); c.append((abs(math.log(mu/target)), p, N, mu))
        c.sort()
        for _, p, N, mu in c[:2]:
            print(f"n={n} {fam} p={p} N={N} 2N={2*N} mu={mu:.2f} dev={100*(mu/target-1):+.0f}%")
