import math
W = 883708281  # W(14,9) = 1 + 14*(13 + 13^3 + 13^5 + 13^7)
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
qs = [q for q in range(8, 20000) if q % 7 == 1 and isprime(q)]
for p in (29, 41, 43, 71, 127, 139, 97, 83):
    for fam, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
        for n in [1] + qs:
            if math.gcd(p, n) != 1: continue
            N = base * n
            if N > 1.5e8: break
            if N < 1e7: continue
            mu = N * math.exp(-W / N)
            if 8 <= mu <= 32: print(f"{fam} {p} {n} N={N} mu={mu:.2f}")
