import math, sys
sys.path.insert(0, '/home/user/degree-diameter/research/frontier/beyond11')
W = 883708281  # W(14,9)
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
k = int(sys.argv[1]); targets = [10, 15, 20, 25, 30]
best = {t: None for t in targets}
for p in range(5, 400):
    if not isprime(p): continue
    if k > 2 and (p - 1) % k and (p + 1) % k and p != k: continue
    for fam, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
        for n in [1] + [q for q in range(2, 3000) if isprime(q) and q % k == 1 and math.gcd(p, q) == 1]:
            if math.gcd(p, n) != 1: continue
            N = base * n
            if N > 6.5e7: break
            if N < 5e7: continue
            mu = N * math.exp(-W / N)
            for t in targets:
                if abs(mu - t) < 1.0 and (best[t] is None or abs(mu - t) < best[t][0]):
                    best[t] = (abs(mu - t), fam, p, n, N, mu)
for t in targets:
    b = best[t]
    print(t, "->", "none" if b is None else f"{b[1]} {b[2]} {b[3]} N={b[4]} mu={b[5]:.2f}")
